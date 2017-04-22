{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}
module DataTypes where

{-@ die :: {v:String | false} -> a  @-}
die = error


{-@ data IncList a =
        Emp
      | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}}  @-}
data IncList a
  = Emp
  | (:<) { hd :: a
      ,  tl :: IncList a}

infixr 9 :<

{-@ type IncListBig a x = IncList {v:a | x <= v} @-}
{-@ type IncListSmall a x = IncList {v:a | v <= x} @-}
okList = 1 :< 2 :< 3 :< Emp -- accepted by LH

insert
  :: (Ord a)
  => a -> IncList a -> IncList a
insert y Emp = y :< Emp
insert y (x :< xs)
  | y <= x = y :< x :< xs
  | otherwise = x :< insert y xs

insertSort'
  :: (Ord a)
  => [a] -> IncList a
insertSort' xs = foldr insert Emp xs

split :: [a] -> ([a], [a])
split (x:y:zs) = (x : xs, y : ys)
  where
    (xs, ys) = split zs
split xs = (xs, [])

quickSort
  :: (Ord a)
  => [a] -> IncList a
quickSort [] = Emp
quickSort (x:xs) = append x lessers greaters
  where
    lessers = quickSort [y | y <- xs, y < x]
    greaters = quickSort [z | z <- xs, z >= x]

{-@ append :: x:a -> IncListSmall a x
                  -> IncListBig a x
                  -> IncList a
  @-}
append :: a -> IncList a -> IncList a -> IncList a
append z Emp ys = z :< ys
append z (x :< xs) ys = x :< append z xs ys

------------------
data BST a
  = Leaf
  | Node { root :: a
        ,  left :: BST a
        ,  right :: BST a}

{-@
data BST a = Leaf
            | Node { root  :: a
                   , left  :: BSTL a root
                   , right :: BSTR a root }
@-}
{-@ type BSTL a X = BST {v:a | v < X} @-}
{-@ type BSTR a X = BST {v:a | v > X} @-}

okBST :: BST Int
okBST =
  Node
    6
    (Node 2 (Node 1 Leaf Leaf) (Node 4 Leaf Leaf))
    (Node 9 (Node 7 Leaf Leaf) Leaf)

mem
  :: (Ord a)
  => a -> BST a -> Bool
mem _ Leaf = False
mem x (Node v l r)
  | x == v = True
  | x < v = mem x l
  | otherwise = mem x r


one   :: a -> BST a
one x = Node x Leaf Leaf

add                  :: (Ord a) => a -> BST a -> BST a
add k Leaf = one k
add k t@(Node x l r)
  | k < x = Node x (add k l) r
  | k < x = Node x l (add k r)
  | otherwise = t


{-@ type NotLeaf a = {v:BST a | notLeaf v} @-}
{-@ measure notLeaf @-}
notLeaf :: BST a -> Bool
notLeaf Leaf = False
notLeaf (Node _ _ _) = True

-- this value is lower than the rest of the tree
data MinPair a = MP { mElt :: a, rest :: BST a }
{-@ data MinPair a = MP { mElt :: a, rest :: BSTR a mElt} @-}

{-@ delMin :: NotLeaf a -> MinPair a @-}
delMin                 :: (Ord a) => BST a -> MinPair a
delMin (Node k Leaf r) = MP k r
delMin (Node k l r)    = MP k' (Node k l' r)
  where
    MP k' l'           = delMin l
delMin Leaf            = die "Don't say I didn't warn ya!"


del                   :: (Ord a) => a -> BST a -> BST a
del k' t@(Node k l r)
  | k < x = Node x (del k l) r
  | k < x = Node x l (del k r)
  | otherwise = Leaf
del _  Leaf           = Leaf
