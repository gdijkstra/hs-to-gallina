{-# OPTIONS_HsToGallina bc: log #-}

module Log where

data Nat = Zero
         | Succ Nat

div2 :: Nat -> Nat
div2 Zero = Zero
div2 (Succ Zero) = Zero
div2 (Succ (Succ n)) = Succ (div2 n)

log :: Nat -> Nat
log (Succ Zero) = Zero
log (Succ (Succ p)) = Succ (log (Succ (div2 p)))
