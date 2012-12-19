{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_HsToGallina co: Stream trues #-}

module CoinductionExample where

data Stream a = Cons a (Stream a)

data Bool = True | False

trues :: Stream Bool
trues = Cons True trues

