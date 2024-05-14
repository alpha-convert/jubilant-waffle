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

data Ty = TyEps | TyInt | TyCat Ty Ty deriving (Eq,Ord,Show)

isNull :: Ty -> Bool
isNull TyEps = True
isNull TyInt = False
isNull (TyCat {}) = False

data Term where
    EpsR :: Term
    IntR :: Int -> Term
    Var :: String -> Ty -> Term
    IntCase :: String -> Term -> Term -> Term
    CatL :: String -> String -> String -> Term -> Term
    CatR :: Ty -> Term -> Term -> Term

data Event = IntEv Int | CatEvA Event | CatPunc deriving (Eq,Ord,Show)
    -- IntEv :: Int -> Event
    -- ListEvDone :: Event
    -- ListEvNext :: Event
    -- CatEvA :: Event -> Event
    -- CatPunc :: Event


data TaggedEvent = TEV String Event deriving (Eq,Ord,Show)

deriv :: Ty -> Event -> Ty
deriv TyEps _ = error ""
deriv TyInt (IntEv _) = TyEps
deriv TyInt _ = error ""
deriv (TyCat s t) (CatEvA ev) = TyCat (deriv s ev) t
deriv (TyCat _ t) CatPunc = t
deriv (TyCat {}) _ = error ""

isDone :: Event -> State Ty Bool
isDone ev = do
    t <- get
    put (deriv t ev)
    return (isNull (deriv t ev))

isNotDone ev = not <$> isDone ev

varIsNotDone x (TEV y ev) | x == y = isNotDone ev
varIsNotDone x (TEV y ev) = return True

peelTag x (TEV y ev) | x == y = Just ev
peelTag x (TEV y ev) = Nothing

derivStream :: Ty -> Stream Event -> Stream Ty
derivStream t0 (S (SF x0 next)) = S (SF (x0,t0) next')
    where
        next' (next -> Done,t) = Done
        next' (next -> Skip x,t) = Skip (x,t)
        next' (next -> Yield ev x,t) =
            let t' = deriv t ev in
            Yield t' (x,t')

varTake :: String -> Ty -> Stream TaggedEvent -> Stream Event
varTake x t0 (S (SF x0 next)) = S (SF (x0,t0,False) next')
    where
        next' (_,_,True) = Done
        next' (next -> Done,_,_) = Done
        next' (next -> Skip x',t,_) = Skip (x',t,False)
        next' (next -> Yield (TEV y ev) x',t,_) | y /= x = Skip (x',t,False)
        next' (next -> Yield (TEV y ev) x',t,_) | y == x =
            let t' = deriv t ev in
            Yield ev (x',t',isNull t')

varDrop :: String -> Ty -> Stream TaggedEvent -> Stream TaggedEvent
varDrop x t0 (S (SF x0 next)) = S (SF (x0,t0,False) next')
    where
        next' (next -> Done,_,True) = Done
        next' (next -> Skip x',t,True) = Skip (x',t,True)
        next' (next -> Yield tev x',t,True) = Yield tev (x',t,True)

        next' (next -> Done,_,False) = Done
        next' (next -> Skip x',t,False) = Skip (x',t,False)
        next' (next -> Yield (TEV y ev) x',t,False) | y /= x = Skip (x',t,False)
        next' (next -> Yield (TEV y ev) x',t,False) | y == x =
            let t' = deriv t ev in
            Skip (x',t',isNull t')

denote :: Term -> Stream TaggedEvent -> (Stream Event, Stream TaggedEvent)
denote EpsR s = (mempty,s)
denote (IntR n) s = (scons (IntEv n) mempty,s)
denote (Var x t) s = (varTake x t s,varDrop x t s)

denote (IntCase x e1 e2) s =
    let startOfX = sdropWhile (\(TEV y _) -> y /= x) s in
    let (e1out,e1rest) = denote e1 (stail startOfX) in
    let (e2out,e2rest) = denote e2 (sapplyFirst intPred startOfX) in
    (sIf ifz startOfX e1out e2out,sIf ifz startOfX e1rest e2rest)
        where
            ifz (TEV _ (IntEv 0)) = True
            ifz (TEV _ (IntEv _)) = False
            intPred (TEV x (IntEv n)) = TEV x (IntEv (n - 1))

denote (CatL x y z e) s = denote e (sstatefulmap False (undefined go) s)
    where
        go (TEV z' (CatEvA ev)) False | z == z' = (False,Just (TEV x ev))
        go (TEV z' CatPunc) False | z == z' = (True,Nothing)
        go (TEV z' ev) True | z == z' = (True,Just (TEV y ev))
        go tev@(TEV {}) b = (b,Just tev)

denote (CatR _ e1 e2) s =
    let (e1out,srest) = denote e1 s in
    let (e2out,srest') = denote e2 srest in
    (fmap CatEvA e1out <> pure CatPunc <> e2out,srest')

main = return ()

data Chan = VarChan String | Proj1Chan Chan | Proj2Chan Chan

data Autom where
    Stop :: Autom
    Output :: Int -> Autom
    UseChan :: Chan -> Ty -> Autom
    IfZ :: Chan -> Autom -> Autom -> Autom
    Then :: Ty -> Autom -> Autom -> Autom

t2a :: Term -> Autom
t2a e = go mempty e
    where
        getChan m x = case Map.lookup x m of
                      Nothing -> VarChan x
                      Just c -> c
        go _ EpsR = Stop
        go _ (IntR n) = Output n
        go m (Var x s) = UseChan (getChan m x) s
        go m (IntCase z e1 e2) =
            let c = getChan m z in
            IfZ c (go m e1) (go m e2)
        go m (CatR s e1 e2) = Then s (go m e1) (go m e2)
        go m (CatL x y z e) =
            let c = getChan m z in
            go (Map.insert x (Proj1Chan c) (Map.insert y (Proj2Chan c) m)) e

denoteAutom :: Autom -> StreamFunc s TaggedEvent -> StreamFunc (s,Autom) Event
denoteAutom e (SF x0 next_in) = SF (x0,e) next
    where

        nextFromChan x' (VarChan x) =
            (case next_in x' of
                Done -> Done
                Skip x'' -> Skip x''
                Yield (TEV z ev) x'' -> if z == x then Yield ev x'' else Skip x'', VarChan x)
        nextFromChan x' (Proj1Chan c) =
            case nextFromChan x' c of
                (Done,c') -> (Done,Proj1Chan c')
                (Skip x'',c') -> (Skip x'',Proj1Chan c')
                (Yield (CatEvA ev) x'',c') -> (Yield ev x'', Proj1Chan c')
                (Yield {},_)-> error ""
        nextFromChan x' (Proj2Chan c) =
                case nextFromChan x' c of
                (Done,c') -> (Done,Proj2Chan c')
                (Skip x'',c') -> (Skip x'',Proj2Chan c')
                (Yield CatPunc x'',c') -> (Skip x'', c') -- peel off the proj2. this is probably not an ideal way to do this, but oh well. should really be in-place.
                (Yield {},_)-> error ""

        next (x',e@(UseChan c s)) =
            if isNull s
            then Done
            else 
                case nextFromChan x' c of
                    (Done,c') -> Done
                    (Skip x'',c') -> Skip (x'',UseChan c' s)
                    (Yield ev x'',c') -> Yield ev (x'',UseChan c' (deriv s ev))

        next (x',Output n) = Yield (IntEv n) (x',Stop)

        next (x',Stop) = Done

        next (x',IfZ c e1 e2) =
            case nextFromChan x' c of
                (Done,c') -> Done
                (Skip x',c') -> Skip (x',IfZ c' e1 e2)
                (Yield (IntEv 0) x',_) -> Skip (x',e1)
                (Yield (IntEv _) x',_) -> Skip (x',e2)

        next (x',Then s e1 e2) =
            if isNull s then Yield CatPunc (x',e2)
            else case next (x',e1) of
                Done -> Skip (x',e2)
                Skip (x'',e1') -> Skip (x'',Then s e1' e2)
                Yield ev (x'',e1') -> Yield (CatEvA ev) (x'',Then (deriv s ev) e1' e2)

{-

G |-_{G |- e} e : s
--------------------
G |-_{...} fix e : s


---------------------
G |-_{G |- s} rec : s

-}