module SimpleExample where

data B = T 
       | F

data Nat = Zero | Succ Nat

data ListB = Nil
           | Cons B ListB

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
