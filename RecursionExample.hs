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
              

data B = T | F

not :: B -> B
not T = id F
not F = id T

id :: a -> a
id a = a

data Zig = ZigC Zag

data Zag = ZagC Zig

test :: Nat -> B -> B
test Zero = id
test (Succ k) = not

idBool :: B -> B
idBool = id

