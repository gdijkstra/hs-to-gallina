{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_Hs2Gallina log quicksort predCheck #-}

module BCExample where

data Nat = Zero
         | Succ Nat

data List a = Nil
            | Cons a (List a)

data Bool = True
          | False

-- From the Coq'art book:
-- div2 :: Nat -> Nat
-- div2 Zero = Zero
-- div2 (Succ Zero) = Zero
-- div2 (Succ (Succ n)) = Succ (div2 n)

-- log :: Nat -> Nat
-- log (Succ Zero) = Zero
-- log (Succ (Succ p)) = Succ (log (Succ (div2 p)))

-- From the "Modelling general recursion..." paper:

filter :: (a -> Bool) -> List a -> List a
filter p Nil         = Nil
filter p (Cons x xs) = case p x of
  True -> Cons x (filter p xs)
  False -> filter p xs


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

--predCheck :: List (List Nat) -> List Nat -> List Nat
--predCheck (Cons x xs) = append x xs

quicksort :: List Nat -> List Nat
quicksort Nil         = Nil
quicksort (Cons x xs) = append
                        (quicksort (filter ((flip lt) x) xs))
                        (quicksort (filter ((flip ge) x) xs))
