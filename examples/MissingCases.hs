{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_HsToGallina bc: missing0 missing1 hd recursive #-}

module MissingCases where

-- "Prelude":
data Nat = Zero
         | Succ Nat

data List a = Nil
            | Cons a (List a)

data Bool = True
          | False

const :: a -> b -> a
const a _ = a

id :: a -> a
id x = x

missing0 :: List Nat -> Bool
missing0 (Cons Zero Nil) = True

missing1 :: List Nat -> Bool -> Bool
missing1 (Cons Zero Nil) True = True

hd :: List a -> a
hd (Cons x _xs) = x


recursive :: List Nat -> Bool
recursive (Cons Zero Nil ) = True
recursive (Cons _x (Cons _y x)) = id (recursive x)

