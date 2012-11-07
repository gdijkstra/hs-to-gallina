{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_Hs2Gallina missing0 recursive #-}

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

-- recursive :: List Nat -> Bool
-- recursive (Cons Zero Nil ) = True
-- recursive (Cons _x (Cons _y x)) = id (recursive x)

