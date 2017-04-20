{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module MeasureNum
where

import Prelude  hiding  (map, zipWith, zip, take, drop, reverse)

{-@ type TRUE = {v: Bool | v} @-}
{-@ type Pos = {v: Int | v > 0} @-}
{-@ type Nat = {v: Int | v >= 0} @-}


{-@ die :: {v:String | false} -> a  @-}
die = error


{-@ measure notEmpty @-}
notEmpty :: [a] -> Bool
notEmpty []  = False
notEmpty (_:_) = True


{-@ measure size @-}
{-@ size    :: xs:[a] -> {v:Nat | v = len xs} @-}
size :: [a] -> Int
size []     = 0
size (_:rs) = 1 + size rs


type List a = [a]
{-@ type ListN a N = {v:List a | len v = N} @-}
{-@ type ListX a X = ListN a {len X}        @-}
{-@ type ListXY a X Y = ListN a {len X + len Y}        @-}

{-@ map      :: (a -> b) -> xs:List a-> ListX b xs @-}
map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs


{-@ prop_map :: List a-> TRUE @-}
prop_map :: [a] -> Bool
prop_map xs = length xs == length ys
  where
    ys      = map id xs


{-@ zipWith :: (a -> b -> c) -> xs:List a
                             -> ListX b xs
                             -> ListX c xs
  @-}
zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
zipWith _ [] []         = []
zipWith _ _  _          = die "no other cases"

{-@ type ListGE a N = {v:List a | N <= size v} @-}
{-@ type ListG a N = {v:List a | N < size v} @-}

{-@ take'     :: n:Nat -> ListG a n -> ListN a n @-}
take' :: Int -> List a -> List a
take' 0 _      = []
take' n (x:xs) = x : take' (n-1) xs
take' _ _      = die "won't  happen"
