module Lesson02

import Data.Vect

%default total

tup : (Int, Bool, Double, Integer)
tup = (1, ?nested)

io : IO ()
io = putStrLn "Labas"

nn : Nat
nn = 45

ll : List a -> Nat
ll [] = Z
ll (x :: xs) = S (ll xs)

mutual
    isEven : Nat -> Bool
    isEven 0 = True
    isEven (S k) = isOdd k

    isOdd : Nat -> Bool
    isOdd 0 = False
    isOdd (S k) = isEven k

v0 : Vect 0 Int
v0 = []

v4 : Vect 4 Double
v4 = [1,2,3,4]

allLength : Vect l String -> Vect l Nat
allLength [] = []
allLength (x :: xs) = length x :: allLength xs

insertion : Ord el => el -> Vect len el -> Vect (S len) el
insertion x [] = [x]
insertion x (y :: xs) = case x < y of
                             False => y :: insertion x xs
                             True => x :: (y :: xs)

insSort : Ord el => Vect n el -> Vect n el
insSort [] = []
insSort (x :: xs) = let sorted = insSort xs in
                        insertion x sorted

addMatrics : Num e => Vect row (Vect col e) -> 
                      Vect row (Vect col e) ->
                      Vect row (Vect col e)

mulMatrics : Num e => Vect n (Vect m e) ->
                      Vect m (Vect p e) ->
                      Vect n (Vect p e)

empties' : (n : Nat) ->  Vect n (Vect 0 e)
empties' 0 = []
empties' (S k) = [] :: empties' k

empties : {n : Nat} -> Vect n (Vect 0 e)
empties {n = 0} = []
empties {n = (S k)} = [] :: empties {n=k}

transposeHelp : Vect n e -> Vect n (Vect len e) -> Vect n (Vect (S len) e)
transposeHelp [] [] = []
transposeHelp (x :: xs) (y :: ys) = (x :: y) :: transposeHelp xs ys

transposeMat : {n:Nat} -> Vect m (Vect n e) -> Vect n (Vect m e)
transposeMat [] = empties' n
transposeMat (x :: xs) = let transposed = (transposeMat xs) in
                             transposeHelp x transposed

append : Vect n e -> Vect m e -> Vect (n+m) e
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

Vec : Nat -> Type-> Type
Vec=Vect

length : {n: Nat} -> Vect n e -> Nat
length {n} _ = n

lll : List Nat
lll = do
    a <- [1,2,3]
    b <- [4,5,6]
    c <- [7,8,9]
    [a, b, c]

vvv : Vect 3 Nat
vvv = do
    a <- [1,2,3]
    b <- [4,5,6]
    c <- [7,8,9]
    [a, b, c]

vv : Vect 2 Nat
vv = do
    a <- [1,2]
    b <- [4,5]
    c <- [7,8]
    [a, c]