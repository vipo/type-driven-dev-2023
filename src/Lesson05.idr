module Lesson05

import Data.Vect

%default total

occurences : Eq ty => (item: ty) -> (values: List ty) -> Nat
occurences item [] = 0
occurences item (x :: xs) = case item == x of
                                 False => (occurences item xs)
                                 True => 1 + (occurences item xs)

data Matter = Solid | Liquid | Gas

Eq Matter where
  (==) Solid Solid = True
  (==) Liquid Liquid = True
  (==) Gas Gas = True
  (==) _ _ = False

data Tree e = Empty | Node (Tree e) e (Tree e)

Eq e => Eq (Tree e) where
    (==) Empty Empty = True
    (==) (Node l v r) (Node l' v' r') = l == l' && r == r' && v == v'
    (==) _ _ = False

tree1 : Tree Nat
tree1 = Node Empty 10 (Node Empty 15 (Node Empty 20 Empty))

record Album where
    constructor MkAlbum
    artist : String
    title : String
    year : Integer

a1 : Album
a1 = (MkAlbum "A1" "t1" 2000)

a2 : Album
a2 = (MkAlbum "A1" "t2" 2000)

Eq Album where
  (==) (MkAlbum a1 t1 y1) (MkAlbum a2 t2 y2) = a1 == a2 && t1 == t2 && y1 == y2

Ord Album where
    compare (MkAlbum a1 t1 y1) (MkAlbum a2 t2 y2) =
        case compare a1 a2 of
            EQ => case compare t1 t2 of
                EQ => compare y1 y2
                diff_t => diff_t
            diff_art => diff_art

Show Album where
    show (MkAlbum artist title year) = artist ++ " " ++ title ++ " (" ++ show year ++ ")"

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Abs (Expr num)

expr : Expr Nat
expr = Add (Val 1) (Mul (Val 4) (Abs (Val (-6))))

eval : (Num num, Integral num, Abs num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Mul x y) = eval x * eval y
eval (Abs x) = abs (eval x)

Num ty => Num (Expr ty) where
    (+) = Add
    a * b = Mul a b
    fromInteger = Val . fromInteger

Num ty => Abs (Expr ty) where
    abs = Abs

Cast (Maybe a) (List a) where
    cast Nothing = []
    cast (Just x) = [x]

Foldable (\a => Tree a) where
    foldr f acc Empty = acc
    foldr f acc (Node left e right) =
        let leftFold = foldr f acc left
            rightFold = foldr f leftFold right in
            f e rightFold

