{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Main where
import Data.Functor.Const
import Control.Monad (void, liftM2)
import Control.Monad.Identity (Identity(runIdentity))
import qualified Data.Bifunctor
import Control.Applicative (liftA2)
import Control.Monad.State.Strict
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as Map
import Distribution.Compat.Lens (_1)

main = return ()

{- Inspired by "Stream Fusion" -}

{-

s ::= int | (s;s) | s*

e ::= 

g := x1 : int; ... ; xn : int

-}

data Step s a where
    Done :: Step s a
    Skip :: s -> Step s a
    Yield :: a -> s -> Step s a

stepStateMap :: (s -> s') -> Step s a -> Step s' a
stepStateMap f Done = Done
stepStateMap f (Skip x) = Skip (f x)
stepStateMap f (Yield a x) = Yield a (f x)

data StreamFunc s a where
    SF :: forall s a. s %1 -> (s -> Step s a) %1 -> StreamFunc s a

data Stream a where
    S :: forall a s. StreamFunc s a -> Stream a

ssink :: Stream a
ssink = S $ SF () (const Done)

ssing :: a -> Stream a
ssing x = S $ SF False (\b -> if not b then Yield x True else Done)

srepeat :: a -> Stream a
srepeat x = S $ SF () $ const $ Yield x ()

scons :: a -> Stream a -> Stream a
scons a (S (SF x0 next)) = S $ SF Nothing $
    \case
        Nothing -> Yield a (Just x0)
        Just (next -> Done) -> Done
        Just (next -> Skip x) -> Skip (Just x)
        Just (next -> Yield a x) -> Yield a (Just x)

stail :: Stream a -> Stream a
stail (S (SF x0 next)) = S $ SF (x0,False) $
    \case
        (next -> Done,_) -> Done
        (next -> Skip x,b) -> Skip (x,b)
        (next -> Yield a x,False) -> Skip (x,True)
        (next -> Yield a x,True) -> Yield a (x,True)

smap :: (a -> b) -> Stream a -> Stream b
smap f (S (SF x0 next)) = S $ SF x0 $
    \case
        (next -> Done) -> Done
        (next -> Skip x) -> Skip x
        (next -> Yield a x) -> Yield (f a) x

smapMaybe :: (a -> Maybe b) -> Stream a -> Stream b
smapMaybe f (S (SF x0 next)) = S $ SF x0 $
    \case
        (next -> Done) -> Done
        (next -> Skip x) -> Skip x
        (next -> Yield (f -> Nothing) x) -> Skip x
        (next -> Yield (f -> Just b) x) -> Yield b x

sfilter :: (a -> Bool) -> Stream a -> Stream a
sfilter f = smapMaybe (\x -> if f x then Just x else Nothing)

sstatefulmap :: s -> (a -> State s (Maybe b)) -> Stream a -> Stream b
sstatefulmap y0 f (S (SF x0 next)) = S $ SF (x0,y0) $
    \case
        (next -> Done,_) -> Done
        (next -> Skip x,y) -> Skip (x,y)
        (next -> Yield a x,y) -> case runState (f a) y of
                                    (Just b,y') -> Yield b (x,y')
                                    (Nothing,y') -> Skip (x,y')

sapplyFirst :: (a -> a) -> Stream a -> Stream a
sapplyFirst f = sstatefulmap False $ \a -> do
    pastFirst <- get
    if pastFirst then do
        return (Just a)
    else do
        put True
        return (Just (f a))

sbind :: Stream a -> (a -> Stream b) -> Stream b
sbind (S (SF x0 next)) f = S $ SF (x0,Nothing) $
    \case
        (x',Just (S (SF x'' next'))) -> case next' x'' of
                                            Done -> Skip (x', Nothing)
                                            Skip x''' -> Skip (x', Just (S (SF x''' next')))
                                            Yield b x''' -> Yield b (x', Just (S (SF x''' next')))
        (next -> Done,Nothing) -> Done
        (next -> Skip x,Nothing) -> Skip (x,Nothing)
        (next -> Yield a x,Nothing) -> Skip (x, Just (f a))


statefulSBind :: Stream a -> s -> (s -> a -> (s, Stream b)) -> Stream b
statefulSBind (S (SF x0 next)) y0 f = S $ SF (x0,y0,Nothing) $
    \case
        (x',y',Just (S (SF x'' next'))) -> case next' x'' of
                                            Done -> Skip (x',y', Nothing)
                                            Skip x''' -> Skip (x', y',Just (S (SF x''' next')))
                                            Yield b x''' -> Yield b (x', y', Just (S (SF x''' next')))
        (next -> Done,y,Nothing) -> Done
        (next -> Skip x,y,Nothing) -> Skip (x,y,Nothing)
        (next -> Yield a x,y,Nothing) -> let (y',bs) = f y a in
                                         Skip (x,y', Just bs)

szip :: Stream a -> Stream b -> Stream (a,b)
szip (S (SF x0 next)) (S (SF y0 next')) = S $ SF (x0,y0,Nothing) $
    \case
        (next -> Done,y,Nothing) -> Done
        (next -> Skip x',y,Nothing) -> Skip (x',y,Nothing)
        (next -> Yield a x',y,Nothing) -> Skip (x',y,Just a)
        (x,next' -> Done,Just a) -> Done
        (x,next' -> Skip y',Just a) -> Skip (x,y',Just a)
        (x,next' -> Yield b y',Just a) -> Yield (a,b) (x,y',Nothing)

sconcat :: Stream a -> Stream a -> Stream a
sconcat (S (SF x0 next)) (S (SF y0 next')) = S $ SF (Left x0) $
    \case
        (Left (next -> Done)) -> Skip (Right y0)
        (Left (next -> Skip x)) -> Skip (Left x)
        (Left (next -> Yield a x)) -> Yield a (Left x)
        (Right (next' -> Done)) -> Done
        (Right (next' -> Skip y)) -> Skip (Right y)
        (Right (next' -> Yield a y)) -> Yield a (Right y)

{-
sconcat ssink s
  = sconcat (S $ SF () (const Done)) (S (SF y0 next')) 
  = S $ (SF (Left ())) $
        \case
            (Left (const Done -> Done)) -> Skip (Right y0)
            (Left (const Done -> Skip x)) -> Skip (Left x)
            (Left (const Done -> Yield a x)) -> Yield a (Left x)
            (Right (next' -> Done)) -> Done
            (Right (next' -> Skip y)) -> Skip (Right y)
            (Right (next' -> Yield a y)) -> Yield a (Right y)
  =  S $ (SF (Left ())) $
        \case
            (Left ()) -> Skip (Right y0)
            (Right (next' -> Done)) -> Done
            (Right (next' -> Skip y)) -> Skip (Right y)
            (Right (next' -> Yield a y)) -> Yield a (Right y)
  ~= s (bisimulation: equivalent up to skips.)
-}

yieldStates :: StreamFunc s a -> StreamFunc s s
yieldStates (SF x0 next) = SF x0 $
    \case
        (next -> Done) -> Done
        (next -> Skip x) -> Yield x x
        (next -> Yield _ x) -> Yield x x

stakeWhile :: (a -> Bool) -> Stream a -> Stream a
stakeWhile p (S (SF x0 next)) = S $ SF x0 next'
    where
        next' (next -> Done) = Done
        next' (next -> Skip x) = Skip x
        next' (next -> Yield a x) = if p a then Yield a x else Done


stakeWhileSt :: s -> (a -> State s Bool) -> Stream a -> Stream a
stakeWhileSt x0 f (S (SF y0 next)) = S (SF (y0,x0) next')
    where
        next' (next -> Done,_) = Done
        next' (next -> Skip y,x) = Skip (y,x)
        next' (next -> Yield a y,x) = let (b,x') = runState (f a) x in if b then Yield a (y,x') else Done

sdropWhile :: (a -> Bool) -> Stream a -> Stream a
sdropWhile p (S (SF x0 next)) = S $ SF (x0,True) next'
    where
        next' (next -> Done,_) = Done
        next' (next -> Skip x,b) = Skip (x,b)
        next' (next -> Yield a x,False) = Yield a (x,True)
        next' (next -> Yield a x,True) = if p a then Skip (x,True) else Yield a (x,False)

sdropWhileSt :: s -> (a -> State s Bool) -> Stream a -> Stream a
sdropWhileSt x0 f (S (SF y0 next)) = S (SF (y0,x0,True) next')
    where
        next' (next -> Done,_,_) = Done
        next' (next -> Skip y,x,b) = Skip (y,x,b)
        next' (next -> Yield a y,x,False) = Yield a (y,x,False)
        next' (next -> Yield a y,x,True) = let (b,x') = runState (f a) x in if b then Skip (y,x',True) else Yield a (y,x',False)


sspan :: (a -> Bool) -> Stream a -> (Stream a, Stream a)
sspan p s = (stakeWhile p s, sdropWhile p s)

-- (sappend (stakewhile p s) (sdropwhile p s)) == s

spartition :: (a -> Either b c) -> Stream a -> (Stream b, Stream c)
spartition f (S (SF x0 next)) = (S (SF x0 next1), S (SF x0 next2))
    where
        next1 (next -> Done) = Done
        next1 (next -> Skip x) = Skip x
        next1 (next -> Yield (f -> Left b) x) = Yield b x
        next1 (next -> Yield (f -> _) x) = Skip x

        next2 (next -> Done) = Done
        next2 (next -> Skip x) = Skip x
        next2 (next -> Yield (f -> Right c) x) = Yield c x
        next2 (next -> Yield (f -> _) x) = Skip x
{-
alternatively, spartition f s = smux (srepeat f) s
-}

sFromList :: [a] -> Stream a
sFromList = foldr scons ssink

sToList :: Stream a -> [a]
sToList = foldr (\x xs -> xs ++ [x]) []

instance Show a => Show (Stream a) where
    show = show . sToList

sMux :: Stream (a -> Either b c) -> Stream a -> (Stream b,Stream c)
sMux fs as =
    let ebcs = (\(f,a) -> f a) <$> szip fs as in
    (ebcs >>= either return (const mempty),ebcs >>= either (const mempty) return)

sRepeatFirst :: Stream a -> Stream a
sRepeatFirst (S (SF x0 next)) = S $ SF (x0,Nothing) $
    \case
        (next -> Done,Nothing) -> Done
        (next -> Skip x,Nothing) -> Skip (x,Nothing)
        (next -> Yield a x,Nothing) -> Yield a (x,Just a)
        s@(x,Just a) -> Yield a s



{- applies the condition to the first element of the input stream, and then switches to one or the other -}
sIf :: (a -> Bool) -> Stream a -> Stream b -> Stream b -> Stream b
sIf p (S (SF x0 next)) (S (SF y0 next0)) (S (SF y1 next1)) = S (SF (Left x0) next')
    where
        next' (Left (next -> Done)) = Done
        next' (Left (next -> Skip x)) = Skip (Left x)
        next' (Left (next -> Yield a _)) = if p a then Skip (Right (Left y0)) else Skip (Right (Right y1))
        next' (Right (Left (next0 -> Done))) = Done
        next' (Right (Left (next0 -> Skip y))) = Skip (Right (Left y))
        next' (Right (Left (next0 -> Yield b y))) = Yield b (Right (Left y))
        next' (Right (Right (next1-> Done))) = Done
        next' (Right (Right (next1 -> Skip y))) = Skip (Right (Right y))
        next' (Right (Right (next1 -> Yield b y))) = Yield b (Right (Right y))


instance Monad Stream where
    return = pure
    (>>=) = sbind

instance Applicative Stream where
    pure = ssing
    liftA2 = liftM2

instance Foldable Stream where
    foldr f y0 (S (SF x0 next)) = go (x0,y0)
        where
            go (next -> Done,y) = y
            go (next -> Skip x,y) = go (x,y)
            go (next -> Yield a x,y) = go (x,f a y)

instance Semigroup (Stream a) where
    (<>) = sconcat

instance Monoid (Stream a) where
    mempty = ssink

{- unclear if this instance behaves well with regards to fusion... probably depends on f? -}
instance Traversable Stream where
    traverse f (S (SF x0 next)) = go x0
        where
            go (next -> Done) = pure ssink
            go (next -> Skip x) = go x
            go (next -> Yield a x) = scons <$> f a <*> go x

instance Functor Stream where
    fmap :: (a -> b) -> Stream a -> Stream b
    fmap f (S (SF x next)) = S $ SF x $
        \case
            (next -> Done) -> Done
            (next -> Skip x) -> Skip x
            (next -> Yield a x) -> Yield (f a) x

data Ty = TyEps | TyInt | TyCat Ty Ty | TyPlus Ty Ty | TyStar Ty deriving (Eq,Ord,Show)

isNull :: Ty -> Bool
isNull TyEps = True
isNull TyInt = False
isNull (TyCat {}) = False
isNull (TyPlus {}) = False
isNull (TyStar {}) = False

data Term where
    {-
    --------------
    G |- EpsR : eps
    -}
    EpsR :: Term
    {-
    -----------------------
    G;x:s;G' |- Var x s : s
    -}
    Var :: String -> Ty -> Term
    {-
    -----------------
    G |- IntR n : Int
    -}
    IntR :: Int -> Term
    {-
    G' |- e1 : s
    y:Int;G' |- e2 : s
    ------------------------------------
    G;x:Int;G' |- IntCase x e1 y e2 : s
    -}

    IntCase :: String -> Term -> String -> Term -> Term

    {-
    G;x:s;y:t;G' |- e : r
    ----------------------------
    G;z:s.t;G' |- CatL x y z e : r
    -}
    CatL :: String -> String -> String -> Term -> Term
    {-
    G |- e1 : s
    D |- e2 : t
    ----------------------
    G;D |- (e1;e2) : s . t
    -}
    CatR :: Ty -> Term -> Term -> Term
    {-
    -}
    InL :: Term -> Term
    InR :: Term -> Term
    PlusCase :: String -> String -> Term -> String -> Term -> Term
    Nil :: Term
    Cons :: Term -> Term -> Term
    StarCase :: String -> Term -> String -> String -> Term -> Term
    Fix :: Term -> Term
    Rec :: Term
    deriving (Eq,Ord,Show)

data Event = IntEv Int | CatEvA Event | CatPunc | PlusPuncA | PlusPuncB deriving (Eq,Ord,Show)

data TaggedEvent = TEV String Event deriving (Eq,Ord,Show)

deriv :: Ty -> Event -> Ty
deriv TyEps _ = error ""
deriv TyInt (IntEv _) = TyEps
deriv TyInt _ = error ""
deriv (TyCat s t) (CatEvA ev) = TyCat (deriv s ev) t
deriv (TyCat _ t) CatPunc = t
deriv (TyCat {}) _ = error ""
deriv (TyPlus s _) PlusPuncA = s
deriv (TyPlus _ t) PlusPuncB = t
deriv (TyPlus {}) _ = error ""
deriv (TyStar _) PlusPuncA = TyEps
deriv (TyStar s) PlusPuncB = TyCat s (TyStar s)
deriv (TyStar {}) _ = error ""

{- Are Elims just a focusing thing? -}
data Elim = VarElim String
          | Proj1Elim Elim
          | Proj2Elim Elim
          deriving (Eq,Ord,Show)
{-

Elimnel tying:

-------------------------
G;x:s;G' |- VarElim x : s

G |- c : s . t
---------------------
G |- Proj1Elim c : s

G |- c : s . t
---------------------
G |- Proj2Elim c : t

-}

{- Removes all Pi2s from an eliminator. If we've gotten at least one event through an eliminator, it has to have no more pi2s in it... -}
delPi2 :: Elim -> Elim
delPi2 (VarElim x) = VarElim x
delPi2 (Proj1Elim c) = Proj1Elim (delPi2 c)
delPi2 (Proj2Elim c) = delPi2 c

{- if elim is an eliminator with underlying variable x, and ev is an event from the channel x,
then elimDeriv elim ev is the eliminator updated after the event
-}

{- absolutely no idea how i came up with the code for this. -}
elimDeriv :: Elim -> Event -> Elim
elimDeriv el ev = go el ev const
    where
        go (VarElim x) ev k = k (VarElim x) (Just ev)
        go (Proj1Elim el) ev k = go el ev (\el' ev ->
            case ev of
                Nothing -> k (Proj1Elim el') Nothing
                Just (CatEvA ev') -> k (Proj1Elim el') (Just ev')
         )
        go (Proj2Elim el) ev k = go el ev (\el' ev ->
            case ev of
                Nothing -> k (Proj2Elim el') Nothing
                Just (CatEvA _) -> k (Proj2Elim el') Nothing
                Just CatPunc -> k el' Nothing
         )


data ElimTerm =
      EEpsR
    | EUse Elim Ty
    | EIntR Int
    | ECatR ElimTerm ElimTerm
    | EInR ElimTerm
    | EInL ElimTerm
    | EPlusCase Elim ElimTerm ElimTerm
    | ENil
    | ECons ElimTerm ElimTerm
    | EFix ElimTerm
    | ERec
    deriving (Eq,Ord,Show)

fixSubst :: ElimTerm -> ElimTerm -> ElimTerm
fixSubst = undefined

inlineElims :: Term -> ElimTerm
inlineElims e = go mempty e
    where
        getElim m x = case Map.lookup x m of
                      Nothing -> VarElim x
                      Just c -> c
        go _ EpsR = EEpsR
        go _ (IntR n) = EIntR n
        go m (Var x s) = EUse (getElim m x) s
        -- go m (IntCase z e1 y e2) =
        --     let c = getElim m z in
        --     EIntCase c (go m e1) (go (Map.insert y (PredElim (delPi2 c)) m) e2)
        go m (CatR s e1 e2) = ECatR (go m e1) (go m e2)
        go m (CatL x y z e) =
            let c = getElim m z in
            go (Map.insert x (Proj1Elim c) (Map.insert y (Proj2Elim c) m)) e
        go m (InL e) = EInL (go m e)
        go m (InR e) = EInR (go m e)
        go m (PlusCase z x e1 y e2) =
            let c = getElim m z in
            EPlusCase c (go (Map.insert x (delPi2 c) m) e1) (go (Map.insert y (delPi2 c) m) e2)
        go m Nil = ENil
        go m (Cons e1 e2) = ECons (go m e1) (go m e2)
        go m (StarCase z e1 x xs e2) =
            let c = getElim m z in
            EPlusCase c (go (Map.insert x (Proj1Elim (delPi2 c)) m) e1) (go (Map.insert xs (Proj2Elim (delPi2 c)) m) e2)

denoteElimTerm :: ElimTerm -> StreamFunc s TaggedEvent -> StreamFunc (s,ElimTerm) Event
denoteElimTerm e (SF x0 next_in) = SF (x0,e) next
    where
        nextFromElim x' (VarElim x) =
            case next_in x' of
                Done -> Done
                Skip x'' -> Skip (x'',VarElim x)
                Yield (TEV z ev) x'' -> if z == x then Yield ev (x'',VarElim x) else Skip (x'',VarElim x)

        nextFromElim x' (Proj1Elim c) =
            case nextFromElim x' c of
                Done -> Done
                Skip (x'',c') -> Skip (x'',Proj1Elim c')


                Yield (CatEvA ev) (x'',c') -> Yield ev (x'', Proj1Elim c')


                Yield {} -> error ""
        nextFromElim x' (Proj2Elim c) =
                case nextFromElim x' c of
                    Done -> Done
                    Skip (x'',c') -> Skip (x'',Proj2Elim c')
                    Yield (CatEvA _) (x'',c') -> Skip (x'', Proj2Elim c')

                    Yield CatPunc (x'',c') -> Skip (x'', c') -- peel off the proj2. this is probably not an ideal way to do this, but oh well. should really be in-place.

                    Yield {} -> error ""

        next (x',e@(EUse c s)) =
            if isNull s
            then Done
            else case nextFromElim x' c of
                    Done -> Done
                    Skip (x'',c') -> Skip (x'',EUse c' s)
                    Yield ev (x'',c') -> Yield ev (x'',EUse c' (deriv s ev))

        next (x',EIntR n) = Yield (IntEv n) (x',EEpsR)

        next (x',EEpsR) = Done

        next (x',ECatR e1 e2) =
            case next (x',e1) of
                Skip (x'',e1') -> Skip (x'',ECatR e1' e2)
                Done -> Yield CatPunc (x',e2)
                Yield ev (x'',e1') -> Yield (CatEvA ev) (x'',ECatR e1' e2)

        next (x',EInL e) = Yield PlusPuncA (x',e)
        next (x',EInR e) = Yield PlusPuncB (x',e)

        next (x',EPlusCase c e1 e2) =
            case nextFromElim x' c of
                Done -> Done
                Skip (x',c') -> Skip (x',EPlusCase c' e1 e2)
                Yield PlusPuncA (x',_) -> Skip (x',e1)
                Yield PlusPuncB (x',_) -> Skip (x',e2)

        next (x', ENil) = Yield PlusPuncA (x',EEpsR)
        next (x', ECons e1 e2) = Yield PlusPuncB (x',ECatR e1 e2)

        next (x', EFix e) = Skip (x', fixSubst (EFix e) e)
        next (x', ERec) = error ""

denoteElimTerm' a (S sf) = S (denoteElimTerm a sf)

type StateId = Int

data EventShape = ESIntEv | ESCatEvA EventShape | ESCatPunc | ESPlusPuncA | ESPlusPuncB deriving (Eq,Ord,Show)

shapeOf :: Event -> EventShape
shapeOf (IntEv _) = ESIntEv
shapeOf (CatEvA ev) = ESCatEvA (shapeOf ev)
shapeOf CatPunc = ESCatPunc
shapeOf PlusPuncA = ESPlusPuncA
shapeOf PlusPuncB = ESPlusPuncB

data OutputModifier = OId | AddCatEvA OutputModifier

data ReadyElim = VarReadyElim String | Proj1ReadyElim ReadyElim {- these are fully-deriv'd elims: the next event you pull on the underlying channel has to be for for it.  -}

applyOutputModifier :: OutputModifier -> Event -> Event
applyOutputModifier OId = id
applyOutputModifier (AddCatEvA om) = CatEvA . applyOutputModifier om

data Action =
      SStop
    | SPrepareElim String (Map EventShape StateId) -- state in which you chew off data for a the elim until it's ``ready''
    | SForwardInput ReadyElim OutputModifier (Map EventShape StateId)
    | SOutput Event StateId
    | SBranch ReadyElim StateId StateId
    | SJump StateId

addCatEvA SStop = SStop
addCatEvA a@(SPrepareElim {}) = a
addCatEvA (SForwardInput el om jt) = SForwardInput el (AddCatEvA om) jt
addCatEvA (SOutput ev j) = SOutput (CatEvA ev) j
addCatEvA a@(SBranch {}) = a
addCatEvA a@(SJump {}) = a

data Autom = A { states :: Map StateId Action }

buildAutom :: ElimTerm -> (Int,Autom)
buildAutom e = let (init,states) = fst (runState (go (-1) e) (0,Nothing)) in (init,A states)
    where
        freshStateId :: State (Int,Maybe Int) Int
        freshStateId = do
            (n,mf) <- get
            put (n+1,mf)
            return n
        getFixStart :: State (Int,Maybe Int) Int
        getFixStart = do
            (n,mf) <- get
            return (fromMaybe (error "") mf)
        setFixStart f = do
            (n,mf) <- get
            put (n, Just f)
        eraseFixStart :: State (Int,Maybe Int) ()
        eraseFixStart = do { (n,_) <- get; put (n, Nothing)}

        go end EEpsR = do
            n <- freshStateId
            return (n,Map.singleton n (SJump end))
        go end (EUse elim ty) = _
        go end (EIntR k) = do
            n <- freshStateId
            return (n,Map.singleton n (SOutput (IntEv k) end))
        go end (ECatR e1 e2) = do
            puncNode <- freshStateId
            (e1start,m1) <- go puncNode e1
            (e2start,m2) <- go end e2
            let m1' = fmap addCatEvA m1
            return (e1start,Map.insert puncNode (SOutput CatPunc e2start) (Map.union m1' m2))
        go end (EInL e) = do
            puncNode <- freshStateId
            (estart,m) <- go end e
            return (puncNode,Map.insert puncNode (SOutput PlusPuncA estart) m)
        go end (EInR e) = do
            puncNode <- freshStateId
            (estart,m) <- go end e
            return (puncNode,Map.insert puncNode (SOutput PlusPuncB estart) m)

        go end (EFix e) = do
            fixStart <- freshStateId
            setFixStart fixStart
            (estart, m) <- go end e
            eraseFixStart
            return (fixStart, Map.insert fixStart (SJump estart) m)
        go end ERec = do
            recNode <- freshStateId
            fixAddr <- getFixStart
            return (recNode, Map.singleton recNode (SJump fixAddr))

denoteAutom :: StateId -> Autom -> StreamFunc s TaggedEvent -> StreamFunc (s,Int) Event
denoteAutom n (A m) (SF x0 next_in) = SF (x0,n) go
    where
        go (x,n) = let action = Map.lookup n m in next x n (fromMaybe (error "") action)

        nextFromVar x' var =
            case next_in x' of
                Done -> Done
                Skip x'' -> Skip x''
                Yield (TEV z ev) x'' -> if z == var then Yield ev x'' else Skip x''

        nextFromReadyElim x' (VarReadyElim x) = nextFromVar x' x
        nextFromReadyElim x' (Proj1ReadyElim c) =
            case nextFromReadyElim x' c of
                Done -> Done
                Skip x'' -> Skip x''
                Yield (CatEvA ev) x'' -> Yield ev x''
                Yield {} -> error ""

        next x _ SStop = Done
        next x n (SPrepareElim var jumpTable) =
            case nextFromVar x var of
                Done -> Done
                Skip x' -> Skip (x',n)
                Yield ev x' ->
                    let jumpTarget = fromMaybe (error "") (Map.lookup (shapeOf ev) jumpTable) in
                    Skip (x',jumpTarget)

        next x _ (SOutput ev n') = Yield ev (x,n')
        next x n (SBranch re t1 t2) =
            case nextFromReadyElim x re of
                Done -> Done
                Skip x' -> Skip (x',n)
                Yield PlusPuncA x' -> Skip (x',t1)
                Yield PlusPuncB x' -> Skip (x',t2)

        next x _ (SJump n') = Skip (x,n')


