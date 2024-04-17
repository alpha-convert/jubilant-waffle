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
        (next -> Yield a x,False) -> Skip (x,False)
        (next -> Yield a x,True) -> Yield a (x,True)

smap :: (a -> b) -> Stream a -> Stream b
smap f (S (SF x0 next)) = S $ SF x0 $
    \case
        (next -> Done) -> Done
        (next -> Skip x) -> Skip x
        (next -> Yield a x) -> Yield (f a) x

sstatefulmap :: s -> (a -> s -> (s,Maybe b)) -> Stream a -> Stream b
sstatefulmap y0 f (S (SF x0 next)) = S $ SF (x0,y0) $
    \case
        (next -> Done,_) -> Done
        (next -> Skip x,y) -> Skip (x,y)
        (next -> Yield a x,y) -> case f a y of
                                    (y',Just b) -> Yield b (x,y')
                                    (y',Nothing) -> Skip (x,y')

sapplyFirst :: (a -> a) -> Stream a -> Stream a
sapplyFirst f = sstatefulmap False $ curry $
    \case
        (a,False) -> (True, Just (f a))
        (a,True) -> (True, Just a)

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

sdropWhile :: (a -> Bool) -> Stream a -> Stream a
sdropWhile p (S (SF x0 next)) = S $ SF (x0,False) next'
    where
        next' (next -> Done,_) = Done
        next' (next -> Skip x,b) = Skip (x,b)
        next' (next -> Yield a x,True) = Yield a (x,True)
        next' (next -> Yield a x,False) = if p a then Skip (x,False) else Yield a (x,True)

ssplitOn :: (a -> Bool) -> Stream a -> (Stream a, Stream a)
ssplitOn p s = (stakeWhile p s, sdropWhile p s)

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
sToList = foldr (:) []

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
sIf :: (a -> Bool) -> Stream a -> (Stream a, Stream a)
sIf p (S (SF x0 next)) = (S $ SF (x0,False) yes, S $ SF (x0,False) no)
    where
        yes (next -> Skip x,False) = Skip (x,False)
        yes (next -> Yield a x, False) = if p a then Yield a (x,True) else Done
        yes (x,True) = stepStateMap (,True) $ next x

        no (next -> Skip x,False) = Skip (x,False)
        no (next -> Yield a x, False) = if not (p a) then Yield a (x,True) else Done
        no (x,True) = stepStateMap (,True) $ next x


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

data Term where
    -- EpsR :: Term
    -- Nil :: Term
    Var :: String -> Term
    IntCase :: String -> Term -> Term -> Term
    CatL :: String -> String -> String -> Term -> Term
    -- Cons :: Term -> Term -> Term
    -- CatR :: Term -> Term -> Term

data Event where
    IntEv :: Int -> Event
    -- ListEvDone :: Event
    -- ListEvNext :: Event
    CatEvA :: Event -> Event
    CatPunc :: Event

data TaggedEvent = TEV String Event

-- catSwitch :: (MonadError SemError m) => Ty -> MSF m TaggedEvent [Event] -> MSF m TaggedEvent [Event] -> MSF m TaggedEvent [Event]
-- catSwitch s m1 m2 = dSwitch (feedback s ((m1 *** returnA) >>> (maximalCheck &&& msfDeriv))) (const m2)
--     where
--         maximalCheck = arrM $ \(evs,s') ->
--                 if Event.isMaximal s' evs then
--                     return (fmap CatEvA evs ++ [CatPunc], Just ())
--                 else
--                     return (fmap CatEvA evs, Nothing)


denote :: Term -> (Stream TaggedEvent -> Stream Event)
-- denote EpsR _ = ssink
-- denote Nil _ = return ListEvDone
denote (Var x) (S (SF st next)) = S $ SF st $
    \case
        (next -> Skip st) -> Skip st
        (next -> Done) -> Done
        (next -> Yield (TEV y ev) st) | x == y -> Yield ev st
        (next -> Yield _ st) -> Skip st
denote (IntCase x e1 e2) s =
    let s' = sdropWhile (\(TEV y _) -> y /= x) s in
    let (syes,sno) = sIf ifz s' in
    _ -- denote e1 (stail syes) <> denote e2 (sapplyFirst intPred sno)
        where
            ifz (TEV _ (IntEv 0)) = True
            ifz (TEV _ (IntEv _)) = False
            intPred (TEV x (IntEv n)) = TEV x (IntEv (n - 1))

denote (CatL x y z e) s = denote e (sstatefulmap False go s)
    where
        go (TEV z' (CatEvA ev)) False | z == z' = (False,Just (TEV x ev))
        go (TEV z' CatPunc) False | z == z' = (True,Nothing)
        go (TEV z' ev) True | z == z' = (True,Just (TEV y ev))
        go tev@(TEV {}) b = (b,Just tev)

-- denote (Cons e1 e2) s@(S @st x0 f) =
--     let r = denote e1 s in
--     let u = \x' -> denote e2 (S x' f) in
--     S _ _
--     run e1

-- denote (TmCatR _ e1 e2) = switch (denote e1 >>^ maximalPass) (\p -> applyToFirst id (CatPB p) (denote e2))
--     where
--         maximalPass p = (CatPA p,if isMaximal p then Just p else Nothing)

main = return ()