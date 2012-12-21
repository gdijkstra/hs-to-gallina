module PreludeTest where

idTest :: Bool
idTest = id True

constTest :: a -> ()
constTest = const ()


flipTest :: Bool -> Bool -> Bool
flipTest = let or' True _ = True
               or' _ True = True
               or' _ _    = False
           in flip or'

maybeTest :: Maybe a -> Bool
maybeTest (Just _) = True
maybeTest Nothing  = False

maybeTest' :: Maybe a -> Bool
maybeTest' = maybe False (const True)

eitherTest :: Either a b -> Maybe a
eitherTest (Left a ) = Just a
eitherTest (Right _) = Nothing

-- Interestingly enough, when translating "Just" instead of "\x ->
-- Just x", Coq complains about types not matching. This can be fixed
-- by eta-expanding, as is done here, or by filling in the implicit
-- type parameter.
eitherTest' :: Either a b -> Maybe a
eitherTest' = either (\x -> Just x) (const Nothing)

mapTest :: [a] -> [Bool]
mapTest = map (const True)

filterTest :: [Bool] -> [Bool]
filterTest = filter id

concatMapTest :: [a] -> [a]
concatMapTest = concatMap (\a -> [a,a])

nullTest :: Bool
nullTest = null [Just False]

replicateTest :: [Maybe a]
replicateTest = replicate 10 Nothing

anyTest :: [a] -> Bool
anyTest = any (const True)
