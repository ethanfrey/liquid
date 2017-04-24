{-@ LIQUID "--totalhaskell"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module Terminate
    (
    ) where

import Data.Set hiding (insert)


{-@ type Nat = {v:Int | v >= 0} @-}

{-@ fib :: n:Nat -> Nat @-}
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

{-@ measure elts @-}
{-@ elts :: in:[a] -> {out:Set a| elts in = out} @-}
elts        :: (Ord a) => [a] -> Set a
elts []     = empty
elts (x:xs) = singleton x `union` elts xs

{-@ prove_elts :: _ -> {v:Bool | v} @-}
prove_elts x = (elts x) == (elts x)

{-@ type List a = [a] @-}
{-@ type ListS a S = {v:[a] | elts v = S} @-}
{-@ type ListEmp a = ListS a {Set_empty 0} @-}
{-@ type ListEq a X = ListS a {elts X}    @-}
{-@ type ListSub a X = {v:[a]| Set_sub (elts v) (elts X)} @-}
{-@ type ListUn a X Y = ListS a {Set_cup (elts X) (elts Y)} @-}
{-@ type ListUn1 a X Y = ListS a {Set_cup (Set_sng X) (elts Y)} @-}

{-@ predicate TotSize X V = len (fst V) + len (snd V) == len X @-}
{-@ predicate Half V = 0 <= len (snd V) - len (fst V) && len (snd V) - len (fst V) <= 1 @-}
{-@ predicate Parts X V = Set_cup (elts (fst V)) (elts (snd V)) == (elts X) @-}
{-@ halve :: xs:[a] -> {v:([a], [a]) | TotSize xs v && Parts xs v && Half v} @-}
halve :: [a] -> ([a], [a])
halve (y:z:xs) = ((y:ys), (z:zs)) where (ys, zs) = halve xs
halve xs = ([], xs)

{-@ merge :: xs:List a -> ys:List a -> {zs:ListUn a xs ys | len xs + len ys = len zs} / [len xs + len ys] @-}
merge (x:xs) (y:ys)
  | x <= y           = x : merge xs (y:ys)
  | otherwise        = y : merge (x:xs) ys
merge [] ys          = ys
merge xs []          = xs

{-@ prove_list_eq :: (Ord a) => xs:List a -> y:ListEq a xs @-}
prove_list_eq :: (Ord a) => [a] -> [a]
prove_list_eq [] = []
prove_list_eq (x:[]) = [x]
prove_list_eq (x:xs) = x:(prove_list_eq xs)

{-@ mergeSort :: (Ord a) => xs:List a -> {v:ListEq a xs | len xs == len v} @-}
mergeSort :: (Ord a) => [a] -> [a]
mergeSort []  = []
mergeSort (x:[]) = [x] -- comment out this line to find termination catch a bug
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
   (ys, zs)   = halve xs
