module Lesson06

import Data.Vect
import Decidable.Equality

%default total

-- exactLenght : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
-- exactLenght {m} len input = case m == len of
--                              False => Nothing
--                              True => Just input

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
    Same : (num : Nat) -> EqNat num num

sameS : (k: Nat) -> (j: Nat) -> EqNat k j -> EqNat (S k) (S j)
sameS k k (Same k) = Same (S k)
--sameS k j x = ?fd--Same (S j) -- Same (S k)

checkEqNat : (num1 : Nat) -> (num2: Nat) -> Maybe (EqNat num1 num2)
checkEqNat 0 0 = Just (Same 0)
checkEqNat 0 (S k) = Nothing
checkEqNat (S k) 0 = Nothing
checkEqNat (S k) (S j) = case (checkEqNat k j) of
                              Nothing => Nothing
                              (Just x) => Just (sameS k j x)

exactLenght : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLenght {m} len input = case (checkEqNat m len) of
                                 Nothing => Nothing
                                 (Just (Same blah)) => Just input


--data (=) -> a -> b -> Type where
--    Refl : x = x

checkEqNat' : (num1 : Nat) -> (num2: Nat) -> Maybe (num1 = num2)
checkEqNat' 0 0 = Just Refl
checkEqNat' 0 (S k) = Nothing
checkEqNat' (S k) 0 = Nothing
checkEqNat' (S k) (S j) = case (checkEqNat' k j) of
                               Nothing => Nothing
                               (Just x) => Just (cong S x)

myReverse : {n: Nat} -> Vect n e -> Vect n e
myReverse [] = []
myReverse {n = S k} (x :: xs) = let rev_xs = myReverse xs
                                    result = rev_xs ++ [x] in
                                    rewrite plusCommutative 1 k in result

pEq : S k = k + 1 
pEq = rewrite plusCommutative 1 k in ?fdf

myReverseProof : Vect (plus len 1) e -> Vect (S len) e
myReverseProof xs = rewrite (plusCommutative 1 len) in xs

myReverse' : {n: Nat} -> Vect n e -> Vect n e
myReverse' [] = []
myReverse' (x :: xs) = myReverseProof (myReverse' xs ++ [x])
