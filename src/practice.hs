module Foo where

{-@ type Zero    = {v:Int | v == 0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ type Nat = {v:Int | 0 <= v}        @-}

{-@ type TRUE = {v:Bool | Prop v} @-}


{-@ zero :: Zero @-}
zero  = 0 :: Int

{-@ inc:: Nat -> Nat @-}
inc :: Int -> Int
inc x = x + 1


{-@ die :: {v:String | false} -> a  @-}
die msg = error msg

{-@ divide :: Int -> NonZero -> Int @-}
divide :: Int -> Int -> Int
divide _ 0 = die "divide by zero"
divide n d = n `div` d


avg       :: [Int] -> Int
avg [] = 0
avg xs    = divide total n
  where
    total = sum xs
    n     = length xs


{-@ abs' :: Int -> Nat @-}
abs'           :: Int -> Int
abs' n
  | 0 < n     = n
  | otherwise = 0 - n


{-@ lAssert  :: TRUE -> a -> a @-}
lAssert :: Bool -> a -> a
lAssert True  x = x
lAssert False _ = die "yikes, assertion fails!"

yes = lAssert (1 + 1 == 2) ()
-- no  = lAssert (1 + 1 == 3) ()

truncate :: Int -> Int -> Int
truncate i max
  | i' <= max' = i
  | otherwise  = max' * (i `divide` i')
    where
      i'       = abs' i
      max'     = abs' max
