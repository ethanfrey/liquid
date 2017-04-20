{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module DataTypes
where

{-@ data IncList a =
        Emp
      | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}}  @-}
data IncList a =
    Emp
  | (:<) { hd :: a, tl :: IncList a }

infixr 9 :<

{-@ type IncListBig a x = IncList {v:a | x <= v} @-}
{-@ type IncListSmall a x = IncList {v:a | v <= x} @-}

okList  = 1 :< 2 :< 3 :< Emp      -- accepted by LH

insert             :: (Ord a) => a -> IncList a -> IncList a
insert y Emp       = y :< Emp
insert y (x :< xs)
  | y <= x         = y :< x :< xs
  | otherwise      = x :< insert y xs

insertSort'     :: (Ord a) => [a] -> IncList a
insertSort' xs  = foldr insert Emp xs

split          :: [a] -> ([a], [a])
split (x:y:zs) = (x:xs, y:ys)
  where
    (xs, ys)   = split zs
split xs       = (xs, [])

quickSort           :: (Ord a) => [a] -> IncList a
quickSort []        = Emp
quickSort (x:xs)    = append x lessers greaters
  where
    lessers         = quickSort [y | y <- xs, y < x ]
    greaters        = quickSort [z | z <- xs, z >= x]

{-@ append :: x:a -> IncListSmall a x
                  -> IncListBig a x
                  -> IncList a
  @-}
append :: a -> IncList a -> IncList a -> IncList a
append z Emp       ys = z :< ys
append z (x :< xs) ys = x :< append z xs ys
