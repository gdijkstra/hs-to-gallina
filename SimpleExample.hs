module SimpleExample where

data B = T 
       | F

idB :: B -> B
idB T = T
idB F = F

notB :: B -> B
notB T = F
notB F = T

andB :: B -> B -> B
andB T T = T
andB _ _ = F
