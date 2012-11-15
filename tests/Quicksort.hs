{-# OPTIONS_Hs2Gallina bc: quicksort #-}
module Quicksort where

data Nat = Zero | Succ Nat

lt :: Nat -> Nat -> Bool
lt Zero     Zero     = False
lt Zero     (Succ n) = True
lt (Succ n) Zero     = False
lt (Succ n) (Succ m) = lt n m

ge :: Nat -> Nat -> Bool
ge a b = not (lt a b)

append :: [a] -> [a] -> [a]
append [] ys       = ys
append (x : xs) ys = x : (append xs ys)

quicksort :: [Nat] -> [Nat]
quicksort []       = []
quicksort (x : xs) = append
                     (quicksort (filter ((flip lt) x) xs))
                     (quicksort (filter ((flip ge) x) xs))
