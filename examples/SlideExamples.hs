{-# OPTIONS_HsToGallina bc: quicksort #-}

module SlideExamples where

data List a = Nil
            | Cons a (List a)

myHead :: [a] -> a
myHead (x:xs) = x

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

quicksort' :: [Nat] -> [Nat]S
quicksort' []       = []
quicksort' (x : xs) = append
                     (quicksort' (filter (gt x) xs))
                     (quicksort' (filter (le x) xs))
quicksort :: [Nat] -> [Nat]
quicksort []       = []
quicksort (x : xs) = append
                     (quicksort (filter (gt x) xs))
                     (quicksort (filter (le x) xs))

s :: (a -> b -> c) -> (a -> b) -> a -> c
s p q r = p r (q r)

k :: a -> b -> a
k a _ = a

i :: a -> a
i = s k k
