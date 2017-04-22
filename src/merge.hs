{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module Merge
where

import Prelude hiding (union, elem, insert, mergeSort)
import Data.Set hiding (insert)


{-@ measure elts @-}
elts        :: (Ord a) => [a] -> Set a
elts []     = empty
elts (x:xs) = singleton x `union` elts xs

{-@ type List a = [a] @-}
{-@ type ListLN a N = {v:[a] | len v <= N} @-}
{-@ type ListN a N = {v:[a] | len v == N} @-}

{-@ type ListS a S = {v:[a] | elts v = S} @-}
{-@ type ListEmp a = ListS a {Set_empty 0} @-}
{-@ type ListEq a X = ListS a {elts X}    @-}
{-@ type ListSub a X = {v:[a]| Set_sub (elts v) (elts X)} @-}
{-@ type ListUn a X Y = ListS a {Set_cup (elts X) (elts Y)} @-}
{-@ type ListUn1 a X Y = ListS a {Set_cup (Set_sng X) (elts Y)} @-}

{-@ predicate Parts X A B = Set_cup (elts A) (elts B) = (elts X) @-}
{-@ predicate Down N X A B = (n < 2) || (len A < len X && len B < len X) @-}
{-@ predicate Tot X A B = (len A + len B = len X) @-}
{-@ halve  :: n:Nat -> xs:[a] -> {v:_ | Tot xs (fst v) (snd v) && Down n xs (fst v) (snd v)} / [n] @-}
halve            :: Int -> [a] -> ([a], [a])
halve 0 xs       = ([], xs)
halve n (x:y:zs) = (x:xs, y:ys) where (xs, ys) = halve (n-1) zs
halve _ xs       = ([], xs)

{-@ merge :: xs:List a -> ys:List a -> ListUn a xs ys / [len xs + len ys] @-}
merge (x:xs) (y:ys)
  | x <= y           = x : merge xs (y:ys)
  | otherwise        = y : merge (x:xs) ys
merge [] ys          = ys
merge xs []          = xs

{-@ mergeSort :: (Ord a) => xs:List a -> ListEq a xs @-}
mergeSort :: (Ord a) => [a] -> [a]
mergeSort []  = []
mergeSort (x:[]) = [x]
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
   (ys, zs)   = halve mid xs
   mid        = length xs `div` 2
