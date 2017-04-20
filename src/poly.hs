{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module VectorBounds
where

import Prelude      hiding (head, abs)
import Data.List    (foldl')

{-@ type Nat = {v: Int | v >= 0} @-}
{-@ type Pos = {v: Int | v > 0} @-}

{-@ type List a = [a] @-}
{-@ type ListN a N = {v: [a] | len v == N} @-}
{-@ type ListGN a N = {v: [a] | len v >= N} @-}
{-@ type NEList a = ListGN a 1 @-}

{-@ die :: {v:String | false} -> a  @-}
die msg = error msg

{-@ names :: ListGN String 3 @-}
names = ["foo", "bar", "baz"]

{-@ one :: String @-}
one = (names !! 1)

{-@ head :: NEList a -> a @-}
head :: [a] -> a
head x = x !! 0

{-@ head' :: List a -> Maybe a @-}
head' :: [a] -> Maybe a
head' [] = Nothing
head' (x:_) = Just x

{-@ unsafeLookup :: i: Nat -> {v: List a | len v > i} -> a @-}
unsafeLookup :: Int -> [a] -> a
unsafeLookup index list = list !! index

{-@ safeLookup :: List a -> Int -> Maybe a @-}
safeLookup :: [a] -> Int -> Maybe a
safeLookup x i
  | ok        = Just (x !! i)
  | otherwise = Nothing
  where
    ok        = i >= 0 && i < length x


{-@ sum' :: List Int -> Int @-}
sum' :: [Int] -> Int
sum' (x:xs) = x + sum' xs
sum' [] = 0
-- sum' [] = die "foo"


vsum :: [Int] -> Int
vsum vec     = go 0 0
  where
    go acc i
      | i < sz    = go (acc + (vec !! i)) (i + 1)
      | otherwise = acc
    sz            = length vec
