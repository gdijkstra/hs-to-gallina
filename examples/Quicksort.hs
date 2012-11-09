{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_Hs2Gallina bc: quicksort #-}
module Quicksort where

data Nat =
  Zero
  | Succ Nat

data List a =
  Nil
  | Cons a (List a)

data Bool =
  True
  | False

filter :: (a -> Bool) -> List a -> List a
filter p Nil         = Nil
filter p (Cons x xs) = if p x
                       then Cons x (filter p xs)
                       else filter p xs

lt :: Nat -> Nat -> Bool
lt Zero     Zero     = False
lt Zero     (Succ n) = True
lt (Succ n) Zero     = False
lt (Succ n) (Succ m) = lt n m

not :: Bool -> Bool
not True  = False
not False = True

ge :: Nat -> Nat -> Bool
ge a b = not (lt a b)

flip :: (a -> b -> c) -> b -> a -> c
flip f b a = f a b

append :: List a -> List a -> List a
append Nil ys         = ys
append (Cons x xs) ys = Cons x (append xs ys)

quicksort :: List Nat -> List Nat
quicksort Nil         = Nil
quicksort (Cons x xs) = append
                        (quicksort (filter ((flip lt) x) xs))
                        (quicksort (filter ((flip ge) x) xs))
