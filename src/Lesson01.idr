module Lesson01

%default total

i : Int
i = ?ff

ii : Integer
ii = 42

b : Bool
b = True

f : Bool -> String
f False = "false"
f True = "true"

StringOrInt : Bool -> Type
StringOrInt False = Int
StringOrInt True = String

strOrInt : (x: Bool) -> StringOrInt (not x)
strOrInt False = "labas"
strOrInt True = 42

sar : List Int
sar = []

len : List a -> Int
len [] = 0
len (_ :: xs) = 1 + len xs

prodComm : {a: Type} -> {b: Type} -> (a,b) -> (b,a)
prodComm (x, y) = (y, x)

public export

msg : String
msg = "Everything I Say Will Be On the Exam"