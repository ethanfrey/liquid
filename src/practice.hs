module Foo where

{-@ type Zero    = {v:Int | v == 0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ type Nat   = {v:Int | 0 <= v}        @-}

{-@ zero :: NonZero @-}
zero  = 0 :: Int
