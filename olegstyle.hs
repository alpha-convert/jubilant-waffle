{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Main where
import Data.Functor.Const
import Control.Monad (void)
import Control.Monad.Identity (Identity(runIdentity))



-- data Idx s a where
--     IntIdx :: Idx Int Int
--     CatIdxA :: Idx s a -> Idx (s,t) a
--     CatIdxB :: Idx t a -> Idx (s,t) a
--     StarIdxHere :: Idx s a -> Idx [s] a
--     StarIdxThere :: Idx [s] a -> Idx [s] a

-- data Stream s where
--     S :: forall s da. (forall r a. Idx s a -> (a -> r) -> Maybe r) -> Stream s

-- upFrom :: Int -> Stream [Int]
-- upFrom n = S (go n)
--     where
--         go :: Int -> forall a. forall r. Idx [Int] a -> (a -> r) -> Maybe r
--         go n (StarIdxHere IntIdx) = \k -> Just (k n)
--         go n (StarIdxThere i) = go (n+1) i

-- ssum :: Stream [Int] -> Int
-- ssum (S f) = go (StarIdxHere IntIdx) 0
--     where
--         go :: Idx [Int] Int -> Int -> Int
--         go i n = case f i (+n) of
--                     Just k -> go (StarIdxThere i) k
--                     Nothing -> n


data Eps
class Null a where

instance Null Eps

data Event a da where
    EpsEv :: Event Eps Eps
    IntEv :: Int -> Event Int Eps
    CatEvA :: Event s ds -> Event (s,t) (ds,t)
    CatPunc :: Null s => Event (s,t) t
    ListPuncDone :: Event [s] Eps
    ListPuncIn :: Event [s] (s,[s])

data Events a da where
    NilEvents :: Events s s
    ConsEvents :: Event s ds -> Events ds dds -> Events s dds

data Fold a r where
    FEps :: forall r. r Eps -> Fold Eps r
    F :: forall r a. (forall da. Event a da -> (r da -> r a, Fold da r)) -> Fold a r

data Stream a where
    S :: forall a. (forall r. Fold a r -> r a) -> Stream a

emptyStream :: Stream Eps
emptyStream = S (\(FEps r) -> r)

zero :: Stream Int
zero = S (\(F f) -> let (u,FEps v) = f (IntEv 0) in u v)

fromList :: [Int] -> Stream [Int]
fromList xs = S (go xs)
    where
        go :: [Int] -> Fold [Int] r -> r [Int]
        go [] (F f) = let (u,FEps base) = f ListPuncDone in u base
        go (x:xs) (F f) = let (u,v) = f ListPuncIn in u (go' x xs v)

        go' :: Int -> [Int] -> Fold (Int,[Int]) r -> r (Int,[Int])
        go' x xs (F f) = let (u,v) = f (CatEvA (IntEv x)) in u (go'' xs v)

        go'' :: [Int] -> Fold (Eps,[Int]) r -> r (Eps,[Int])
        go'' xs (F f) = let (u,v) = f CatPunc in u (go xs v)

ssum :: Stream [Int] -> Int
ssum (S k) = getConst (k @(Const Int) (F go))
    where
        go :: Event [Int] da -> (Const Int da -> Const Int [Int], Fold da (Const Int))
        go ListPuncDone = (\(Const x) -> Const x,FEps (Const 0))
        go ListPuncIn = (\(Const x) -> Const x,F go')

        go' :: Event (Int, [Int]) da -> (Const Int da -> Const Int (Int, [Int]), Fold da (Const Int))
        go' (CatEvA (IntEv x)) = (\(Const y) -> Const (x + y),F go'')

        go'' :: Event (Eps, [Int]) da -> (Const Int da -> Const Int (Eps, [Int]), Fold da (Const Int))
        go'' CatPunc = (\(Const x) -> Const x,F go)

fromEvents :: Events s Eps -> Stream s
fromEvents xs = S (go xs)
    where
        go :: Events s Eps -> Fold s r -> r s
        go NilEvents (FEps r) = r
        go (ConsEvents x xs) (F f) = let (u,v) = f x in u (go xs v)

-- zeroes :: Stream [Int]
-- zeroes = S (Folder f1)
--     where
--         f1 :: (forall da. Event [Int] da ->  Folder da r -> r) -> r
--         f1 k = k (Just (ListPuncIn,Folder f2))

--         f2 :: (forall da. Event (Int, [Int]) da -> Folder da r -> r) -> r
--         f2 k = k (Just (CatEvA (IntEv 0),Folder f3))

--         f3 :: (forall da. Event (Eps, [Int]) da -> Folder da r -> r) -> r
--         f3 k = k (Just (CatPunc,Folder f1))

-- ssum :: Stream [Int] -> Int
-- ssum (S (Folder f)) = f (go 0)
--     where
--         go :: Int -> Maybe (Event [Int] da, Folder da Int) -> Int
--         go acc Nothing = acc
--         go acc (Just (ListPuncIn,(Folder f) :: Folder (Int,[Int]) Int)) = f (go' acc)

--         go' :: Int -> Maybe (Event (Int, [Int]) da, Folder da Int) -> Int
--         go' acc Nothing = acc
--         go' acc (Just (CatEvA (IntEv x),(Folder f) :: Folder (Eps,[Int]) Int)) = f (go'' (x + acc))

--         go'' :: Int -> Maybe (Event (Eps, [Int]) da, Folder da Int) -> Int
--         go'' acc Nothing = acc
--         go'' acc (Just (CatPunc,(Folder f) :: Folder [Int] Int)) = f (go acc)

-- double :: Stream [Int] -> Stream [Int]
-- double (S (Folder f)) = f go
--     where
--         go :: Maybe (Event [Int] da, Folder da (Stream [Int])) -> Stream [Int]
--         go Nothing = S (Folder (\k -> k Nothing))
--         go (Just (ListPuncDone))

addUp = ssum (fromList [1,2,3,4])

main = print addUp

-- countUp :: Stream [Int]
-- countUp = S (go 0)
--     where
--         go :: Int -> forall r. (forall da. Event [Int] da -> r da -> r [Int]) -> r [Int]
--         go n k = k @(Int,[Int]) _ _

--         go' :: Int -> forall r. (forall da. Event (Int,[Int]) da -> r da -> r (Int,[Int])) -> r (Int,[Int])
--         go' n k = k (CatEvA (IntEv n)) _

--         go'' :: Int -> forall r. (forall da. Event (Eps,[Int]) da -> r da -> r (Eps,[Int])) -> r (Eps,[Int])
--         go'' n k = k CatPunc (go (n+1) _)