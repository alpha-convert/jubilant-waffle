{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Main where
import Data.Functor.Const



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
    IntEv :: Int -> Event Int Eps
    CatEvA :: Event s ds -> Event (s,t) (ds,t)
    CatPunc :: Null s => Event (s,t) t
    ListPuncDone :: Event [s] Eps
    ListPuncIn :: Event [s] (s,[s])

data Events a da where
    NilEvents :: Events s s
    ConsEvents :: Event s ds -> Events ds dds -> Events s dds

data Folder a r where
    Folder :: ((forall da. Maybe (Event a da,Folder da r) -> r) -> r) -> Folder a r

data Stream a where
    S :: forall a. (forall r. Folder a r) -> Stream a


emptyStream :: Stream Eps
emptyStream = S (Folder (\k -> k Nothing))

fromList :: [Int] -> Stream [Int]
fromList xs = S (Folder (f1 xs))
    where
        f1 :: [Int] -> (forall da. Maybe (Event [Int] da, Folder da r) -> r) -> r
        f1 [] k = k Nothing
        f1 (x:xs) k = k (Just (ListPuncIn,Folder (f2 x xs)))

        f2 :: Int -> [Int] -> (forall da. Maybe (Event (Int, [Int]) da, Folder da r) -> r) -> r
        f2 x xs k = k (Just (CatEvA (IntEv x),Folder (f3 xs)))

        f3 :: [Int] -> (forall da. Maybe (Event (Eps, [Int]) da, Folder da r) -> r) -> r
        f3 xs k = k (Just (CatPunc,Folder (f1 xs)))

zeroes :: Stream [Int]
zeroes = S (Folder f1)
    where
        f1 :: (forall da. Maybe (Event [Int] da, Folder da r) -> r) -> r
        f1 k = k (Just (ListPuncIn,Folder f2))

        f2 :: (forall da. Maybe (Event (Int, [Int]) da, Folder da r) -> r) -> r
        f2 k = k (Just (CatEvA (IntEv 0),Folder f3))

        f3 :: (forall da. Maybe (Event (Eps, [Int]) da, Folder da r) -> r) -> r
        f3 k = k (Just (CatPunc,Folder f1))

ssum :: Stream [Int] -> Int
ssum (S (Folder f)) = f (go 0)
    where
        go :: Int -> Maybe (Event [Int] da, Folder da Int) -> Int
        go acc Nothing = acc
        go acc (Just (ListPuncIn,(Folder f) :: Folder (Int,[Int]) Int)) = f (go' acc)

        go' :: Int -> Maybe (Event (Int, [Int]) da, Folder da Int) -> Int
        go' acc Nothing = acc
        go' acc (Just (CatEvA (IntEv x),(Folder f) :: Folder (Eps,[Int]) Int)) = f (go'' (x + acc))

        go'' :: Int -> Maybe (Event (Eps, [Int]) da, Folder da Int) -> Int
        go'' acc Nothing = acc
        go'' acc (Just (CatPunc,(Folder f) :: Folder [Int] Int)) = f (go acc)

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