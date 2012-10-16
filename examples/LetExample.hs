{-# LANGUAGE NoImplicitPrelude #-}

data List a = Nil
            | Cons a (List a)

foldr :: (a -> b -> b) -> b -> List a -> b
foldr k z = go
  where
    go Nil         = z
    go (Cons y ys) = k y (go ys)

data Unit = Tt

letTest :: List Unit
letTest = let unit = b
              b = Tt
          in Cons unit (Cons unit2 (Cons unit3 Nil))
  where
    unit2 = unit4
    unit3 = unit4
    unit4 = Tt

-- Example of dependency on List where the dependency comes from a
-- constructor used in the "where" part.
lengthTest :: Nat
lengthTest = len test
  where
    len Nil = Zero
    len (Cons _ xs) = Succ (len xs)
    test = Cons Zero (Cons Zero (Cons Zero Nil))

const :: a -> b -> a
const a _ = a

lengthTest' :: Nat
lengthTest' = len test
  where
    len = foldr (const Succ) Zero
    test = Cons Zero (Cons Zero (Cons Zero Nil))

data Nat = Zero
         | Succ Nat
