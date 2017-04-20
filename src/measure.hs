module Measure
where

import Prelude hiding (null, map)

{-@ die :: {v:String | false} -> a  @-}
die = error

{-@ measure notEmpty @-}
notEmpty :: [a] -> Bool
notEmpty []  = False
notEmpty (_:_) = True


{-@ type Pos = {v: Int | v > 0} @-}
{-@ type Nat = {v: Int | v >= 0} @-}
{-@ type NonZero = {v: Int | v /= 0} @-}
{-@ type List a = [a] @-}
{-@ type NEList a = {v:[a] | notEmpty v} @-}

{-@ size :: xs:[a] -> {v:Nat | notEmpty xs => v > 0} @-}
size :: [a] -> Int
size [] = 0
size (_:xs) = 1 + size xs

{-@ divide :: a:Int -> b:NonZero -> {v:Int | a >= 0 && b > 0 ==> v >= 0} @-}
divide :: Int -> Int -> Int
divide x n = x `div` n

{-@ average :: NEList Int -> Int @-}
average :: [Int] -> Int
average xs = divide total elems
  where
    total = sum xs
    elems = size xs

average'      :: [Int] -> Maybe Int
average' xs
  | ok        = Just $ divide (sum xs) elems
  | otherwise = Nothing
  where
    elems     = size xs
    ok        = elems > 0 -- What expression goes here?

{-@ size1    :: xs:NEList a -> Pos @-}
size1 :: [a] -> Int
size1 [] = 0
size1 (_:[]) =  1
size1 (_:xs) =  1 + size1 xs

{-@ size2    :: xs:[a] -> {v:Nat | notEmpty xs => v > 0} @-}
size2 :: [a] -> Int
size2 []     =  0
size2 (_:xs) =  1 + size2 xs

{-@ null :: xs:[a] -> {v: Bool | v <=> len xs == 0} @-}
null :: [a] -> Bool
null []       =  True
null (_:_)    =  False

safeHead      :: [a] -> Maybe a
safeHead xs
  | null xs   = Nothing
  | otherwise = Just $ head xs

{-@ risers   :: (Ord a) => xs:[a] -> {v: [[a]] | notEmpty xs => notEmpty v} @-}
risers           :: (Ord a) => [a] -> [[a]]
risers []        = []
risers [x]       = [[x]]
risers (x:y:etc)
  | x <= y       = (x:s) : ss
  | otherwise    = [x] : (s : ss)
    where
      (s, ss)    = safeSplit $ risers (y:etc)

{-@ safeSplit    :: NEList a -> (a, [a]) @-}
safeSplit (x:xs) = (x, xs)
safeSplit _      = die "don't worry, be happy"

{-@ wtAverage :: NEList (Pos, Pos) -> Nat @-}
wtAverage :: [(Int, Int)] -> Int
wtAverage wxs = divide totElems totWeight
  where
    elems     = map (\(w, x) -> w * x) wxs
    weights   = map (\(w, _) -> w    ) wxs
    totElems  = sum elems
    totWeight = sum weights
    sum       = foldr1 (+)

map           :: (a -> b) -> [a] -> [b]
map _ []      =  []
map f (x:xs)  =  f x : map f xs
