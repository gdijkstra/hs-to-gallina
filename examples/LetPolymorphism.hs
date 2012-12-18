module LetPolymorphism where

not' :: Bool -> Bool
not' b = (myId not) (myId b)
  where
    myId = \x -> x
    