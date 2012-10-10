{-# LANGUAGE NoImplicitPrelude #-}

module RecursionExample where

plus :: Nat -> Nat -> Nat
plus Zero x = x
plus (Succ k) x = Succ (plus k x)

data Nat = Zero
         | Succ Nat

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ e Nil = e
foldr f e (Cons x xs) = f x (foldr f e xs)

data List a = Nil
             | Cons a (List a)

exampleList :: List B
exampleList = Cons T Nil

data B = T | F

not :: B -> B
not T = id F
not F = id T

id :: a -> a
id a = a

test :: Nat -> B -> B
test Zero = idBool
test (Succ k) = not

idBool :: B -> B
idBool = id

-- Simple mutually recursive data types.
data Zig = ZigC Zag

data Zag = ZagC Zig

-- Perfect binary trees
data Pair a = P a a

data Perfect a = Z a
               | S (Perfect (Pair a))

perfect :: Perfect B
perfect = S (Z (P T T))

-- Rose trees
data Rose a = R a (List (Rose a))

rose :: Rose B
rose = R T (Cons (R T Nil) (Cons (R F Nil) Nil))
