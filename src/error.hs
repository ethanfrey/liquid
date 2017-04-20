{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module Error
where

import Prelude hiding (reverse)

type List a = [a]
{-@ type ListN a N = {v:List a | len v = N} @-}
{-@ type ListX a X = ListN a {len X}        @-}

{-@ reverse       :: xs:List a -> ListX a xs @-}
reverse :: List a -> List a
reverse xs        = go [] xs
  where
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs
