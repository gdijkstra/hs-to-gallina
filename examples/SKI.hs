module SKI where

data Foo a = Test a | Tset (Maybe a) () Bool

{-# NOINLINE s #-}
s :: (a -> b -> c) -> (a -> b) -> a -> c
s p q r = p r (q r)

{-# NOINLINE k #-}
k :: a -> b -> a
k a _ = a

{-# NOINLINE i #-}
i :: a -> a
i = s k k
