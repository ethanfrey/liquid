module ArtError () where

import Prelude hiding (break)

{-@ predicate Btwn Lo V Hi = (Lo <= V && V <= Hi) @-}

{-@ data Assoc v <p :: Int -> Bool> = KV ([(Int<p>, v)]) @-}
data Assoc v = KV [(Int, v)]

{-@ digits :: Assoc (String) <{\v -> (Btwn 0 v 9)}> @-}
digits    :: Assoc String
digits    = KV [ (1, "one")
               , (21, "two")
               , (3, "three") ]

data AssocP k v = KVP [(k, v)]

{-@ digitsP :: AssocP {v:Int | (Btwn 0 v 9)} String @-}
digitsP :: AssocP Int String
digitsP = KVP [ (1, "one")
              , (21, "two")
              , (3, "three") ]
