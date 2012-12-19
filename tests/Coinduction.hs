{-# OPTIONS_HsToGallina co: Stream zeroes #-}

module Coinduction where

data Stream a = Cons a (Stream a)

data Nat = Zero | Succ Nat

zeroes :: Stream Nat
zeroes = Cons Zero zeroes
