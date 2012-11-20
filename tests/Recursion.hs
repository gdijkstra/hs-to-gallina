module Recursion where

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ k) x = Succ (plus k x)

data Nat = Zero
         | Succ Nat

exampleList :: [Bool]
exampleList = True : []

test :: Nat -> Bool -> Bool
test Zero = idBool
test (Succ k) = not

idBool :: Bool -> Bool
idBool = id

-- Simple mutually recursive data types.
data Zig = ZigC Zag

data Zag = ZagC Zig

-- Perfect binary trees
data Pair a = P a a

data Perfect a = Z a
               | S (Perfect (Pair a))

perfect :: Perfect Bool
perfect = S (Z (P True True))

-- Rose trees
data Rose a = R a [Rose a]

rose :: Rose Bool
rose = R True ((R True []) : ((R False []) : []))
