{-# OPTIONS_Hs2Gallina bc: bcListTest #-}

module Notation where

-- Booleans
notTest :: Bool -> Bool
notTest b = if b then False else True

-- Unit
unitTest :: () -> ()
unitTest () = ()

-- Lists
listTest :: [a] -> [Bool]
listTest [] = []
listTest [_] = False : []
listTest (_:_:[]) = [True, False]
listTest (_:_:_:[]) = False : [True]
listTest (_:_:_:_:xs) = listTest xs

test :: [a] -> [a]
test [] = []
test (x:_) = [x]

bcListTest :: [a] -> [a]
bcListTest xs = concat (bcListTest xs : [concat [test (bcListTest xs), bcListTest xs]])
