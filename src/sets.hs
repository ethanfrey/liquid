{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module Sets
where

import Prelude hiding (union, elem, insert, mergeSort)
import Data.Set hiding (insert)

{-@ type True  = {v:Bool |     v} @-}
{-@ type False = {v:Bool | not v} @-}

{-@ prop_one_plus_one_eq_two :: _ -> True @-}
prop_one_plus_one_eq_two x   = (x == 1 + 1) `implies` (x == 2)

{-@ type Implies P Q = {v:_ | v <=> (P => Q)} @-}

{-@ implies        :: p:Bool -> q:Bool -> Implies p q  @-}
implies False _    = True
implies _     True = True
implies _    _     = False

{-@ type LT100 = {v:Int | v < 100} @-}
{-@ prop_x_y_200 :: x:LT100 -> y:LT100 -> True  @-}
prop_x_y_200 :: Int -> Int -> Bool
prop_x_y_200 x y = x + y < 200 -- fill in the theorem body

{-@ prop_intersection_comm :: Set -> Set -> True @-}
prop_intersection_comm x y
  = (x `intersection` y) == (y `intersection` x)

{-@ prop_union_assoc :: _ -> _ -> _ -> True @-}
prop_union_assoc x y z
  = (x `union` (y `union` z)) == (x `union` y) `union` z

{-@ prop_intersection_dist :: _ -> _ -> _ -> True @-}
prop_intersection_dist x y z
  =  x `intersection` (y `union` z)
     ==
     (x `intersection` y) `union` (x `intersection` z)

{-@ prop_cup_dif_bad :: Set a -> Set a -> True @-}
prop_cup_dif_bad x y
 = pre `implies` (x == ((x `union` y) `difference` y))
 where
   pre = (x `intersection` y) == empty

--------

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


{-@ append'       :: xs:_ -> ys:_ -> ListUn a xs ys @-}
append' []     ys = ys
append' (x:xs) ys = x : append' xs ys

{-@ reverse' :: xs:[a] -> ListEq a xs @-}
reverse' xs = revHelper [] xs

{-@ revHelper :: xs:[a] -> ys:[a] -> ListUn a xs ys @-}
revHelper acc []     = acc
revHelper acc (x:xs) = revHelper (x:acc) xs

{-@ predicate Parts X A B = Set_cup (elts A) (elts B) = (elts X) @-}
{-@ halve  :: n:Int -> xs:[a] -> {v:_ | Parts xs (fst v) (snd v)} @-}
halve            :: Int -> [a] -> ([a], [a])
halve 0 xs       = ([], xs)
halve n (x:y:zs) = (x:xs, y:ys) where (xs, ys) = halve (n-1) zs
halve _ xs       = ([], xs)

{-@ prop_halve_append  :: _ -> _ -> True @-}
prop_halve_append n xs = elts xs == elts xs'
  where
    xs'      =  append' ys zs
    (ys, zs) =  halve n xs

{-@ elem'      :: (Eq a) => x:a -> xs:[a] -> {v:Bool | v <=> Set_mem x (elts xs) } @-}
elem' _ []     = False
elem' x (y:ys) = x == y || elem' x ys

{-@ test1 :: True @-}
test1      = elem' 2 [1, 2, 3]

{-@ test2 :: False @-}
test2      = elem' 2 [1, 3]

{-@ insert :: x:a -> xs:List a -> ListUn1 a x xs @-}
insert x []     = [x]
insert x (y:ys)
  | x <= y      = x : y : ys
  | otherwise   = y : insert x ys

{-@ insertSort :: (Ord a) => xs:List a -> ListEq a xs @-}
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)

{-@ merge :: xs:List a -> ys:List a -> ListUn a xs ys @-}
merge (x:xs) (y:ys)
  | x <= y           = x : merge xs (y:ys)
  | otherwise        = y : merge (x:xs) ys
merge [] ys          = ys
merge xs []          = xs

{-@ prop_merge_app   :: _ -> _ -> True   @-}
prop_merge_app xs ys = elts zs == elts zs'
  where
    zs               = append' xs ys
    zs'              = merge   xs ys

{-@ mergeSort :: (Ord a) => xs:List a -> ListEq a xs @-}
mergeSort []  = []
mergeSort (x:[])  = [x]
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
   (ys, zs)   = halve mid xs
   mid        = length xs `div` 2
