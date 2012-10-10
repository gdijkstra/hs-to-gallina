data Unit = Tt

data List a = Nil
            | Cons a (List a)

foldr :: (a -> b -> b) -> b -> List a -> b
foldr k z = go
  where
    go Nil         = z
    go (Cons y ys) = k y (go ys)

letTest :: List Unit
letTest = let unit = b
              b = Tt
          in Cons unit (Cons unit2 (Cons unit3 Nil))
  where
    unit2 = unit4
    unit3 = unit4
    unit4 = Tt

