module RecursionExample where

data Nat = Zero
         | Succ Nat

-- idNat :: Nat -> Nat
-- idNat Zero = Zero
-- idNat (Succ k) = Succ (idNat k)

a, b, c, d, e :: Iets
a  = b

b  = c

c c = d

e = \b -> a

d = e
