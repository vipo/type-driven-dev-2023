module Lesson04

import Data.String
import Data.Vect
import System.REPL

%default total

-- readVect' : {l : Nat} -> IO (Vect l String)
-- readVect' = do x <- getLine
--                case x == "" of
--                  True => pure []
--                  False => do xs <- readVect'
--                              pure x :: xs

covering
readVect : IO (len ** Vect len String)
readVect = do x <- getLine
              case x == "" of
                 True => pure (_ ** [])
                 False => do (_ ** xs) <- readVect
                             pure (_ ** x :: xs)

dp : (len ** Vect len String)
dp = (2 ** ["labas", "medis"])

Position : Type
Position = (Double, Double)

-- adder 0 10 = 10
-- adder 1 10 10 = 20
-- adder 2 10 5 5 = 20

AdderType : (numargs: Nat) -> Type
AdderType 0 = Int
AdderType (S k) = (next : Int) -> AdderType k

adder : (numargs: Nat) -> (acc: Int) -> AdderType numargs
adder 0 acc = acc
adder (S k) acc = \next => adder k (acc + next)

-- printf("%s = %d", "el", 42)

data Format = Number Format
            | Str Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType (Number x) = (i: Int) -> PrintfType x
PrintfType (Str x) = (s: String) -> PrintfType x
PrintfType (Lit str x) = (PrintfType x)
PrintfType End = String

printFmt : (fmt : Format) -> (acc: String) -> PrintfType fmt
printFmt (Number x) acc = \i => printFmt x (acc ++ show i)
printFmt (Str x) acc = \s => printFmt x (acc ++ s)
printFmt (Lit str x) acc = printFmt x (acc ++ str)
printFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
toFormat (x :: xs) = Lit (pack [x]) (toFormat xs)

-- printf "%s = %d" -> String -> Numb -> Strin
-- printf "%d" -> Numb -> Strin
-- printf "=" -> Strin

infixr 5 .+.

data Schema = SString
           | SInt
           | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
    constructor MkData
    schema : Schema
    size : Nat
    items : Vect size (SchemaType schema)

addToTail : Vect s t -> t -> Vect (S s) t
addToTail [] item = [item]
addToTail (x :: xs) item = x :: addToTail xs item

addToStore : (store : DataStore) -> (SchemaType (schema store)) -> DataStore
addToStore (MkData s size items) item =
     MkData s (S size) (addToTail items item)

display : {schema : Schema} -> SchemaType schema -> String
display {schema = SString} x = x
display {schema = SInt} x = show x
display {schema = (y .+. z)} (x, w) = "(" ++ display x ++ "," ++ display w ++ ")"

getEntry : (pos : Integer) -> (dataStore: DataStore) -> Maybe String
getEntry pos dataStore = case integerToFin pos (size dataStore) of
                              Nothing => Nothing
                              (Just x) => Just(display(index x (items dataStore)))
