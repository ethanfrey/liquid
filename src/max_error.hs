{-@ LIQUID "--totalhaskell"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module MaxError () where

{-@ maxInt :: forall <p :: Int -> Bool>. Int<p> -> Int<p> -> Int<p> @-}
maxInt     :: Int -> Int -> Int
maxInt x y = if x <= y then y else x

{-@ maximumInt :: forall <p :: Int -> Bool>. {x:[Int <p>] | len x > 0} -> Int <p> @-}
maximumInt :: [Int] -> Int
maximumInt (x:xs) = foldr maxInt x xs
