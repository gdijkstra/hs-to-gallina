module PatExh where

import           Control.Arrow
import           Control.Monad
import           Data.Maybe
import           Debug.Trace
import           System.IO.Unsafe
import           System.Random

data GallinaPat =
  GallinaPVar String
  | GallinaPApp String [GallinaPat]
    deriving (Show, Eq)

data GallinaType =
  GallinaTyApp GallinaType GallinaType
  | GallinaTyVar String
  | GallinaTyCon String
    deriving (Show, Eq)

testPats :: [GallinaPat]
testPats =
  [ GallinaPApp "Zero" []
  , GallinaPApp "Succ" [GallinaPApp "Succ" [GallinaPApp "Zero" []]]
  ]

testPatsInc :: [GallinaPat]
testPatsInc =
  [ GallinaPApp "Zero" []
  , GallinaPApp "Succ" [GallinaPApp "Zero" []]
  ]

-- We assume that length ps0 == length ps1, i.e. no malformed pats.
unify :: GallinaPat -> GallinaPat -> Maybe Substs
unify (GallinaPVar v     ) p = Just $ Subst v p
unify (GallinaPApp _ _   ) (GallinaPVar _) = Nothing
unify (GallinaPApp c0 ps0) (GallinaPApp c1 ps1)
  | c0 /= c1 = Nothing
  | otherwise = do
    substs <- sequence . map (uncurry unify) $ zip ps0 ps1
    return . foldr Compose IdSubst $ substs

missingPats :: [GallinaPat] -> [GallinaPat]
missingPats pats = algorithm initialPatSubs initialIdealPat
  where
    initialPatSubs = map (\x -> (x, Subst idealVar x)) pats
    initialIdealPat = GallinaPVar idealVar
    idealVar = "'ideal"

data Substs =
  Compose Substs Substs
  | Subst String GallinaPat
  | IdSubst
    deriving Show

-- Returns Nothing if the substs only rename variables to variables.
-- Return Just x where x is a variable mapped to a non-variable.
hasNonRenaming :: Substs -> Maybe String
hasNonRenaming IdSubst = Nothing
hasNonRenaming (Subst s p@(GallinaPApp _ _)) = Just s
hasNonRenaming (Subst s (GallinaPVar _)) = Nothing
hasNonRenaming (Compose l r) = hasNonRenaming l `mplus` hasNonRenaming r

algorithm :: [(GallinaPat, Substs)] -> GallinaPat -> [GallinaPat]
algorithm []       idealPat = [idealPat]
algorithm a@((p1, s1):_) idealPat =
  trace ("\nactual pats: " ++ show a ++ "\nideal pat: " ++ show idealPat ++ "\ninvariant holds: " ++ show (invariantHolds a idealPat)) $
  case hasNonRenaming s1 of
    Nothing -> if length a == 1 then [] else error "algorithm: overlap"
    Just x -> let idealPats = splitVar x idealPat
              in trace ("split on: " ++ show x ++ " --> " ++ show idealPats) $
               concatMap (\q -> algorithm (refinePatSubs q a) q) idealPats


refinePatSubs :: GallinaPat -> [(GallinaPat, Substs)] -> [(GallinaPat, Substs)]
refinePatSubs q = mapMaybe (\(pat, substs) -> case unify q pat of
                               Just s -> Just (pat, s)
                               Nothing -> Nothing)


-- Remove all substitutions to variables that do not occur in the
-- given list of variables.
simplify :: [String] -> Substs -> Substs
simplify _    IdSubst = IdSubst
simplify vars s@(Subst var pat) = if var `elem` vars
                                  then s
                                  else IdSubst
simplify vars (Compose l r) = simplify vars l `Compose` simplify vars r


patVars :: GallinaPat -> [String]
patVars (GallinaPVar s    ) = [s]
patVars (GallinaPApp s ps ) = s : concatMap patVars ps


applySubsts :: Substs -> GallinaPat -> GallinaPat
applySubsts IdSubst = id
applySubsts (Compose l r) = applySubsts l . applySubsts r
applySubsts (Subst var pat) = applySubst var pat
  where
    applySubst v0 pat0 pat1@(GallinaPVar v1    ) = if v0 == v1 then pat0 else pat1
    applySubst v0 pat0 (GallinaPApp constr pats) = GallinaPApp constr
                                                   . map (applySubst v0 pat0)
                                                   $ pats

invariantHolds :: [(GallinaPat, Substs)] -> GallinaPat -> Bool
invariantHolds patsSubs idealPat = all (\(a,b) -> a == b)
                                   . map (\(a,b) -> (a, applySubsts b idealPat))
                                   $ patsSubs

-- splitVar should also get the type to find out how we have to split.
splitVar :: String -> GallinaPat -> [GallinaPat]
splitVar var ideal = map (\s -> applySubsts s ideal) substs where
  substs = map (Subst var) pats
  pats = [GallinaPApp "Zero" [], GallinaPApp "Succ" [GallinaPVar "''p"]]


