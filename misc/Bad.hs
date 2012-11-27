-- Stolen from the Agda wiki:
-- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.BadInHaskell

module Bad where

data Bad = BadConstr (Bad -> Bad)

instance Show Bad where
  show (BadConstr _) = "BAD"

omega :: Bad -> Bad
omega f = (case f of (Bad x) -> x) f

loop :: Bad
loop = omega (BadConstr omega)

-- loop = omega (Bad omega) = (case (Bad omega) of (Bad x) -> x) (Bad omega) = omega (Bad omega)