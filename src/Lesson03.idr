module Lesson03

import Data.String
import Data.Vect
import System.REPL

%default total

-- Enumeration
data Direction = North
               | East
               | South
               | West

turnClockwise : Direction -> Direction
turnClockwise North = East
turnClockwise East = South
turnClockwise South = West
turnClockwise West = North

east : Direction
east = East

-- Union
data Shape = Triangle Double Double
           | Rectangle Double Double
%name Shape shape, shape1, shape2

-- Recursive
data Picture = Primitive Shape
             | Combination Picture Picture
             | Rotate Double Picture
%name Picture pic, pic1, pic2

testPicture : Picture
testPicture = Combination (Primitive ?testPicture_rhs_2) (Rotate 43 (Primitive ?testPicture_rhs_5))

pictureArea : Picture -> Double
pictureArea (Primitive shape) = ?pictureArea_rhs_0
pictureArea (Combination pic pic1) = ?pictureArea_rhs_1
pictureArea (Rotate dbl pic) = ?pictureArea_rhs_2

-- Generic

data Tree a = Empty |
              Node (Tree a) a (Tree a)
%name Tree tree, tree1, tree2

insert : Ord e => e -> Tree e -> Tree e
insert x Empty = Node Empty x Empty
insert x orig@(Node left y right) = case compare x y of
                                    LT => Node (insert x left) y right
                                    EQ => orig
                                    GT => Node left y (insert x right)

data BSTree : Type -> Type where
     BSEmpty : Ord e => BSTree e
     BSNode : Ord e => (left: BSTree e) -> e -> (right: BSTree e) -> BSTree e

ins : e -> BSTree e -> BSTree e
ins x BSEmpty = ?ins_rhs_0
ins x (BSNode left y right) = ?ins_rhs_1

-- Dependant

data PowerSource = Petrol | Pedal

data Vehicle : PowerSource -> Type where
     Bicycle : Vehicle Pedal
     Tricycle : Vehicle Pedal
     Car : (fuel : Nat) -> Vehicle Petrol
     Bus : (fuel : Nat) -> Vehicle Petrol

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
--refuel Bicycle impossible

data Vec : Nat -> Type -> Type where
     Nil : Vec Z a
     (::) : (x : a) -> (xs : Vec k a) -> Vec (S k) a
     One : (x : a) -> Vec 1 a 

tryIndex : {n: Nat} -> Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
                         Nothing => Nothing
                         (Just x) => Just(index x xs)

data DataStore : Type where
     MkData : (size : Nat) ->
              (items : Vect size String) ->
              DataStore

size : DataStore -> Nat
size (MkData k _) = k

items : ( store: DataStore) -> Vect (size store) String
items (MkData _ xs) = xs

emptyDataStore : DataStore
emptyDataStore = MkData 0 []

addToTail : Vect size_0 String -> String -> Vect (S size_0) String
addToTail [] str = [str]
addToTail (x :: xs) str = x :: addToTail xs str

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) item =
     MkData (S size) (addToTail items item)

getEntry : (pos : Integer) -> (dataStore: DataStore) -> Maybe String
getEntry pos dataStore = case integerToFin pos (size dataStore) of
                              Nothing => Nothing
                              (Just x) => Just(index x (items dataStore))


data Command = Add String | Get Integer

parseCommand : String -> String -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "get" str = case all isDigit (unpack str) of
                              False => Nothing
                              True => Just (Get (cast str))
parseCommand _ _ = Nothing

parse : String -> Maybe Command
parse str = case span (/= ' ') str of
                        (cmd, arg) => parseCommand cmd (ltrim arg)


processInput : DataStore -> String -> Maybe (String, DataStore)
processInput x str = ?processInput_rhs

-- put vienas
-- put du
-- get 0

covering
main : IO ()
main = replWith (emptyDataStore) ">>> " processInput
