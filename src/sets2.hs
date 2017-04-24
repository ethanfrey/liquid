{-@ LIQUID "--totalhaskell"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module Sets2
    (
    ) where

import Prelude hiding (filter)
import Data.Set hiding (filter)


{-@ type Nat = {v:Int | v >= 0} @-}

{-@ measure elts @-}
{-@ elts :: in:[a] -> {out:Set a| elts in = out} @-}
elts        :: (Ord a) => [a] -> Set a
elts []     = empty
elts (x:xs) = singleton x `union` elts xs

type List a = [a]
{-@ type ListS a S = {v:[a] | elts v = S} @-}
{-@ type ListEmp a = ListS a {Set_empty 0} @-}
{-@ type ListEq a X = ListS a {elts X}    @-}
{-@ type ListSub a X = {v:[a]| Set_sub (elts v) (elts X)} @-}
{-@ type ListUn a X Y = ListS a {Set_cup (elts X) (elts Y)} @-}
{-@ type ListUn1 a X Y = ListS a {Set_cup (Set_sng X) (elts Y)} @-}



{-@ measure unique @-}
unique        :: (Ord a) => List a -> Bool
unique []     = True
unique (x:xs) = unique xs && not (member x (elts xs))

{-@ type UList a = {v:List a | unique v }@-}

{-@ isUnique    :: UList Integer @-}
isUnique        = [1, 2, 3]       -- accepted by LH

-- {-@ isNotUnique :: UList Integer @-}
-- isNotUnique     = [1, 2, 3, 1]     -- rejected by LH

{-@ filter   :: (a -> Bool)
             -> xs:UList a
             -> {v:ListSub a xs | unique v}
  @-}
filter _ []   = []
filter f (x:xs)
  | f x       = x : xs'
  | otherwise = xs'
  where
    xs'       = filter f xs

{-@ filter'   :: (a -> Bool)
             -> xs:List a
             -> {v:ListSub a xs | unique xs => unique v}
  @-}
filter' _ []   = []
filter' f (x:xs)
  | f x       = x : xs'
  | otherwise = xs'
  where
    xs'       = filter' f xs

{-@ test3 :: UList _ @-}
test3     = filter' (> 2) [1,2,3,4]

{-@ test4 :: [_] @-}
test4     = filter' (> 3) [3,1,2,3]

{-@ predicate NoOverlap A B = Set_cap (elts A) (elts B) = Set_empty 0 @-}

{-@ test5 :: {v:([_], [_]) | NoOverlap (fst v) (snd v)} @-}
test5 = ([1, 2, 3], [4, 5, 6])

{-@ reverse    :: xs:UList a -> UList a    @-}
reverse         = go []
  where
    {-@ go     :: a:UList a -> {xs:UList a | NoOverlap a xs} -> UList a / [len xs] @-}
    go a []     = a
    go a (x:xs) = go (x:a) xs

{-@ nub              :: List a -> UList a @-}
nub xs                = go [] xs
  where
    {-@ go              :: acc:UList a -> x:List a -> UList a / [len x] @-}
    go seen []        = seen
    go seen (x:xs)
      | x `isin` seen = go seen     xs
      | otherwise     = go (x:seen) xs

{-@ predicate In X Xs = Set_mem X (elts Xs) @-}
{-@ isin :: x:_ -> ys:_ -> {v:Bool | v <=> In x ys }@-}
isin _ []     = False
isin x (y:ys)
  | x == y    = True
  | otherwise = x `isin` ys

{-@ append       :: xs:UList a -> {ys:UList a | NoOverlap xs ys} -> {v:ListUn a xs ys | unique v} @-}
append []     ys = ys
append (x:xs) ys = x : append xs ys

-- {-@ type Btwn I J = {v:_ | I <= v && v < J} @-}
--
-- {-@ range     :: i:Int -> j:Int -> UList (Btwn i j) @-}
-- range :: Int -> Int -> [Int]
-- range i j
--   | i < j     = i : range (i + 1) j
--   | otherwise = []
