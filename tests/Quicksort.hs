{-# OPTIONS_Hs2Gallina bc: quicksort #-}
module Quicksort where

data Nat = Zero | Succ Nat

-- x > y
gt :: Nat -> Nat -> Bool
gt Zero     Zero     = False
gt Zero     (Succ n) = False
gt (Succ n) Zero     = True
gt (Succ n) (Succ m) = gt n m

-- x <= y
le :: Nat -> Nat -> Bool
le a b = not (gt a b)

append :: [a] -> [a] -> [a]
append [] ys       = ys
append (x : xs) ys = x : (append xs ys)

quicksort :: [Nat] -> [Nat]
quicksort []       = []
quicksort (x : xs) = append
                     (quicksort (filter (gt x) xs))
                     (quicksort (filter (le x) xs))
