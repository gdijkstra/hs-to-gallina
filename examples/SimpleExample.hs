module SimpleExample where

-- idPolymorphic :: a -> a
-- idPolymorphic a = a

-- constPolymorphic :: a -> b -> a
-- constPolymorphic a b = a

-- data B = T 
--        | F

-- idB, notB :: B -> B

-- idB T = T
-- idB F = F

-- notB T = F
-- notB F = T

-- andB :: B -> B -> B
-- andB T T = T
-- andB _ _ = F

-- data List a = Nil
--             | Cons a (List a)

-- data Either a b = Left a
--                 | Right b


data Nat = Zero | Succ Nat

minusOne :: Nat -> Nat
minusOne Zero = Zero
minusOne (Succ k) = k

minusThree :: Nat -> Nat
minusThree = \k -> case k of
  Zero -> Zero
  Succ Zero -> Zero
  Succ (Succ Zero) -> Zero
  (Succ (Succ (Succ k))) -> k

zero :: Nat
zero = Zero

one :: Nat
one = Succ Zero
  
id :: a -> a  
id = \x -> x

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr op e []      = e
foldr op e (x:xs)  = op x (foldr op e xs)
