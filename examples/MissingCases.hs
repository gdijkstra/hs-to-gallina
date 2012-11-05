{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_Hs2Gallina missing0 #-}

module MissingCases where

-- "Prelude":
data Nat = Zero
         | Succ Nat

data List a = Nil
            | Cons a (List a)

data Bool = True
          | False

missing0 :: List Nat -> Bool
missing0 (Cons Zero Nil) = True
