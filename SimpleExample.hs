module SimpleExample where

data B = T 
       | F

data Nat = Zero | Succ Nat

data List a = Nil
            | Cons a (List a)

data Either a b = Left a
                | Right b

data Lam = Var String
         | Abs (Lam -> Lam)


idB, notB, andB :: B -> B

idB T = T
idB F = F

notB T = F
notB F = T

andB T T = T
andB _ _ = F

idPolymorphic :: a -> a
idPolymorphic a = a

constPolymorphic :: a -> b -> a
constPolymorphic a b = a

--minusOne :: Nat -> Nat
--minusOne Zero = Zero
--minusOne (Succ k) = k
