module Coinduction where

import           AG             (Result, coDefinitions, resVernacular)
import qualified Data.Set       as S
import           Gallina.Syntax

-- | Change the fixpoints to cofixpoints for the definitions as
-- specified by the pragmas. Note that we will only change the
-- definitions if all definitions of a mutually recursive group should
-- be read coinductively. We will raise an error otherwise.
makeCoinductive :: Result -> Result
makeCoinductive r = r { resVernacular = v { documentCommands = newDefinitions } }
  where
    v = resVernacular r
    coDefs = coDefinitions r
    oldDefs = documentCommands v
    fixName (Left b) = funName b
    fixName (Right b) = patName b
    newDefinitions = map adaptDefinition oldDefs
    adaptDefinition (GallinaInductive is _) = case allOrNothing (flip S.member coDefs) . map inductiveName $ is of
      Just b -> GallinaInductive is b
      Nothing -> error "makeCoinductive: error."
    adaptDefinition (GallinaFixpoint is _) = case allOrNothing (flip S.member coDefs) . map fixName $ is of
      Just b -> GallinaFixpoint is b
      Nothing -> error "makeCoinductive: error."
    adaptDefinition d = d

-- | Check whether the predicate holds for all elements of the list,
-- or doesn't hold for all the elements of the list. If there's an odd
-- one out, we will return @Nothing@. Otherwise, we will return @Just
-- b@, where @b@ indicates whether the predicate holds for every
-- element of the list. An empty list will yield @Just True@ as a
-- result.
allOrNothing :: (a -> Bool) -> [a] -> Maybe Bool
allOrNothing _ [] = Just True
allOrNothing p xs = foldr1 iff . map (Just . p) $ xs
  where
    iff (Just True) (Just True) = Just True
    iff (Just False) (Just False) = Just False
    iff _ _ = Nothing

