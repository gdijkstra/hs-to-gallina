module SKI where

s :: (a -> b -> c) -> (a -> b) -> a -> c
s p q r = p r (q r)

k :: a -> b -> a
k a _ = a

i :: a -> a
i = s k k
