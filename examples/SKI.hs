module SKI where

s :: (a -> b -> c) -> (a -> b) -> a -> c
s p q r = p r (q r)

k :: a -> b -> a
k a _ = a

-- This works fine in Haskell, but with the current translation of
-- parametric polymorphism, it won't work in Coq. Coq won't be able to
-- infer the implicit parameter b of k.
i :: a -> a
i = s k k

