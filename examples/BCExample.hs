{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_Hs2Gallina log #-}

module BCExample where

-- "Prelude":
data Nat = Zero
         | Succ Nat

data List a = Nil
            | Cons a (List a)

data Bool = True
          | False

-- From the Coq'art book:
div2 :: Nat -> Nat
div2 Zero = Zero
div2 (Succ Zero) = Zero
div2 (Succ (Succ n)) = Succ (div2 n)

log :: Nat -> Nat
log (Succ Zero) = Zero
log (Succ (Succ p)) = Succ (log (Succ (div2 p)))
