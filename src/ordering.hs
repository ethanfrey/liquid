{-@ LIQUID "--totalhaskell"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module Ordering () where

import Prelude hiding (break)

-- Haskell Type Definitions
-- insertSort, mergeSort, quickSort :: (Ord a) => [a] -> [a]

{-@ predicate Btwn Lo V Hi = (Lo <= V && V <= Hi) @-}
data AssocP k v = KVP [(k, v)]

{-@ digitsP :: AssocP {v:Int | (Btwn 0 v 9)} String @-}
digitsP :: AssocP Int String
digitsP = KVP [ (1, "one")
               , (2, "two")
               , (3, "three") ]

{-@ sparseVecP :: AssocP {v:Int | (Btwn 0 v 1000)} Double @-}
sparseVecP :: AssocP Int Double
sparseVecP = KVP [ (12 ,  34.1 )
                 , (92 , 902.83)
                 , (451,   2.95)
                 , (877,   3.1 )]

{-@ data Assoc v <p :: Int -> Bool> = KV (z :: [(Int<p>, v)]) @-}
data Assoc v = KV [(Int, v)]

{-@ digits :: Assoc (String) <{\v -> (Btwn 0 v 9)}> @-}
digits    :: Assoc String
digits    = KV [ (1, "one")
               , (21, "two")
               , (3, "three") ]

{-@ sparseVec :: Assoc Double <{\v -> (Btwn 0 v 1000)}> @-}
sparseVec :: Assoc Double
sparseVec = KV [ (12 ,  34.1 )
                , (92 , 902.83)
                , (451,   2.95)
                , (4877,   3.1 )]

{-@ plusOnes :: [(Int, Int)<{\x1 x2 -> x2 = x1 + 1}>] @-}
plusOnes                         :: [(Int, Int)]
plusOnes = [(0,1), (5,6), (999,1000)]


{-@ predicate Break X Y Z   = (len X) = (len Y) + (len Z) @-}
{-@ break :: (a -> Bool) -> x:[a] -> ([a], [a])<{\y z -> (Break x y z)}> @-}
break                   :: (a -> Bool) -> [a] -> ([a], [a])
break _ xs@[]           =  (xs, xs)
break p xs@(x:xs')
           | p x        =  ([], xs)
           | otherwise  =  let (ys, zs) = break p xs'
                           in (x:ys,zs)

{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}
{-@ type DecrList a = [a]<{\xi xj -> xi >= xj}> @-}
{-@ type UniqList a = [a]<{\xi xj -> xi /= xj}> @-}

{-@ whatGosUp :: IncrList Integer @-}
whatGosUp = [1,2,3]

{-@ noDuplicates :: UniqList Integer @-}
noDuplicates = [1,3,2,5,6]

{-@ insertSort    :: (Ord a) => xs:[a] -> (IncrList a) @-}
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)

{-@ insert :: (Ord a) => a -> IncrList a -> IncrList a @-}
insert y []     = [y]
insert y (x:xs)
  | y <= x      = y : x : xs
  | otherwise   = x : insert y xs

{-@ insertSort' :: (Ord a, Foldable t) => t a -> IncrList a @-}
insertSort' xs  = foldr insert [] xs

{-@ maxInt :: forall <p :: Int -> Bool>. Int<p> -> Int<p> -> Int<p> @-}
maxInt     :: Int -> Int -> Int
maxInt x y = if x <= y then y else x

{-@ maximumInt :: forall <p :: Int -> Bool>. {x:[Int <p>] | len x > 0} -> Int <p> @-}
maximumInt :: [Int] -> Int
maximumInt (x:xs) = foldr maxInt x xs

{-@ maxEvens1 :: xs:[Int] -> {v:Int | (Even v)} @-}
maxEvens1 xs = maximumInt xs''
  where
    xs'      = [ x | x <- xs, isEven x]
    xs''     = 0 : xs'

{-@ predicate Even X = ((X mod 2) = 0) @-}
{-@ isEven :: x:Int -> {v:Bool | (v <=> (Even x))} @-}
isEven   :: Int -> Bool
isEven x = x `mod` 2 == 0


{-@ type Pos  = {v:Int| 0 < v}        @-}
{-@ type Even = {v:Int| v mod 2 == 0} @-}
{-@ type Odd  = {v:Int| v mod 2 /= 0} @-}

{-@ filter3      :: forall a <p :: a -> Bool>.
                      (a -> Maybe a<p>) -> [a] -> [a<p>] @-}
filter3 :: (a -> Maybe a) -> [a] -> [a]
filter3 f []     = []
filter3 f (x:xs) = case f x of
                     Just x'  -> x' : filter3 f xs
                     Nothing ->       filter3 f xs

{-@ mayEven         :: Int -> Maybe Even @-}
mayEven :: Int -> Maybe Int
mayEven x
  | x `mod` 2 == 0 = Just x
  | otherwise      = Nothing

{-@ mayOdd         :: Int -> Maybe Odd @-}
mayOdd :: Int -> Maybe Int
mayOdd x
  | x `mod` 2 == 0 = Nothing
  | otherwise      = Just x


{-@ getEvens3 :: [Int] -> [Even] @-}
getEvens3     = filter3 mayEven

{-@ getOdds3 :: [Int] -> [Odd] @-}
getOdds3     = filter3 mayOdd
