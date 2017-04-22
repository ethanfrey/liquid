module Error2
where

import Prelude hiding (reverse)

{-@ type Nat = {v: Int | v >= 0} @-}

{-@ measure size @-}
{-@ size    :: xs:[a] -> {v:Nat | v = size xs} @-}
size :: [a] -> Int
size []     = 0
size (_:rs) = 1 + size rs

{-@ (:) :: a -> xs:List a -> ListX1 a xs @-}


type List a = [a]
{-@ type ListN a N = {v:List a | size v = N} @-}
{-@ type ListX a X = ListN a {size X}        @-}
{-@ type ListX1 a X = ListN a {1 + size X}        @-}
{-@ type ListXY a X Y = ListN a {size X + size Y}        @-}

{-@ reverse       :: xs:List a -> ListX a xs @-}
reverse :: List a -> List a
reverse xs        = go xs []

{-@ go :: xs:List a -> ys:List a -> ListXY a xs ys @-}
go [] acc     = acc
go (x:xs) acc  = go xs (x:acc)

{-@ reverse'       :: xs:List a -> ListX a xs @-}
reverse' :: List a -> List a
reverse' xs        = go' [] xs

{-@ go' :: xs:List a -> ys:List a -> ListXY a xs ys @-}
go' acc []     = acc
go' acc (x:xs)  = go' (x:acc) xs
