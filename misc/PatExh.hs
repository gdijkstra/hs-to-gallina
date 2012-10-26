module PatExh where

import           Control.Arrow
import           Control.Monad
import           Data.List
import           Data.Maybe
import           Debug.Trace
import           System.Random

data GallinaPatAnnotated =
  GallinaPVarAnn String GallinaType
  | GallinaPAppAnn String [GallinaPatAnnotated]
    deriving (Show, Eq)

type MultiPattern = [GallinaPatAnnotated]

data GallinaPat =
  GallinaPVar String
  | GallinaPApp String [GallinaPat]
    deriving (Show, Eq)

data GallinaType =
  GallinaTyApp GallinaType GallinaType
  | GallinaTyVar String
  | GallinaTyCon String
    deriving (Show, Eq)

testPats :: [MultiPattern]
testPats =
  [ [GallinaPAppAnn "Zero" []]
  , [GallinaPAppAnn "Succ" [GallinaPAppAnn "Succ" [GallinaPAppAnn "Zero" []]]]
  ]

testPatsInc :: [MultiPattern]
testPatsInc =
  [ [GallinaPAppAnn "Zero" [], GallinaPAppAnn "Zero" []]
  , [GallinaPAppAnn "Succ" [GallinaPVarAnn "n" (GallinaTyCon "Nat")], GallinaPAppAnn "Zero" []]
  ]

testMultiPat :: [MultiPattern]
testMultiPat = [ [GallinaPAppAnn "Zero" [], GallinaPVarAnn "x" (GallinaTyCon "Nat")]
               , [GallinaPVarAnn "Succ x" (GallinaTyCon "Nat"), GallinaPAppAnn "Zero" []]
               ]

data MultiPatSubst =
  Compose MultiPatSubst MultiPatSubst
  | Subst String GallinaPatAnnotated
  | IdSubst
    deriving Show

ppMultiPats :: [MultiPattern] -> IO ()
ppMultiPats mp = mapM_ putStrLn $ zipWith (\n p -> show n ++ " " ++ ppMultiPat p) [0..] mp

ppMultiPat :: MultiPattern -> String
ppMultiPat = unwords . intersperse "," . map ppPat

ppPat :: GallinaPatAnnotated -> String
ppPat (GallinaPAppAnn c args) = c ++ " " ++ (unwords . map ppPat $ args)
ppPat (GallinaPVarAnn v _   ) = v

-- We assume that length ps0 == length ps1, i.e. no malformed pats.
unifyMultiPats :: MultiPattern -> MultiPattern -> Maybe MultiPatSubst
unifyMultiPats l r = fmap (foldr Compose IdSubst)
                     $ sequence
                     $ zipWith unifyPatAnn l r

unifyPatAnn :: GallinaPatAnnotated -> GallinaPatAnnotated -> Maybe MultiPatSubst
unifyPatAnn (GallinaPVarAnn v _   ) p = Just $ Subst v p
unifyPatAnn (GallinaPAppAnn _ _   ) (GallinaPVarAnn _ _) = Nothing
unifyPatAnn (GallinaPAppAnn c0 ps0) (GallinaPAppAnn c1 ps1)
  | c0 /= c1 = Nothing
  | otherwise = do
    substs <- sequence . map (uncurry unifyPatAnn) $ zip ps0 ps1
    return . foldr Compose IdSubst $ substs

applyMultiPatSubst :: MultiPatSubst -> MultiPattern -> MultiPattern
applyMultiPatSubst = map . applyPatSubst

applyPatSubst :: MultiPatSubst -> GallinaPatAnnotated -> GallinaPatAnnotated
applyPatSubst IdSubst = id
applyPatSubst (Compose l r) = applyPatSubst l . applyPatSubst r
applyPatSubst (Subst var pat) = applySubst var pat
  where
    applySubst v0 pat0 pat1@(GallinaPVarAnn v1 _  ) = if v0 == v1 then pat0 else pat1
    applySubst v0 pat0 (GallinaPAppAnn constr pats) = GallinaPAppAnn constr
                                                      . map (applySubst v0 pat0)
                                                      $ pats


missingPats :: Int -> [MultiPattern] -> [MultiPattern]
missingPats arity pats = algorithm initialPatSubs initialIdealMultiPat
   where
     initialPatSubs = zipWith (\p q -> (p, fromJust (unifyMultiPats q p)))
                      pats
                      (repeat initialIdealMultiPat)
     initialIdealMultiPat = map (\n -> GallinaPVarAnn (idealVar n) (GallinaTyCon "Nat"))
                            $ [0 .. (arity - 1)]
     idealVar n = "'ideal" ++ show n

-- Returns Nothing if the substs only rename variables to variables.
-- Return Just x where x is a variable mapped to a non-variable.
hasNonRenaming :: MultiPatSubst -> Maybe String
hasNonRenaming IdSubst                          = Nothing
hasNonRenaming (Subst s p@(GallinaPAppAnn _ _)) = Just $ (trace ("found: " ++ s)) s
hasNonRenaming (Subst s (GallinaPVarAnn _ _)  ) = Nothing
hasNonRenaming (Compose l r                   ) = hasNonRenaming l
                                                  `mplus` hasNonRenaming r

algorithm :: [(MultiPattern, MultiPatSubst)] -> MultiPattern -> [MultiPattern]
algorithm []       idealMultiPat = [idealMultiPat]
algorithm a@((p1, s1):_) idealMultiPat =
  trace ("\nactual pats: " ++ show a ++ "\nideal pat: " ++ show idealMultiPat ++ "\ninvariant holds: " ++ show (invariantHolds a idealMultiPat)) $
  case hasNonRenaming s1 of
    Nothing -> if length a == 1 then [] else error "algorithm: overlap"
    Just x -> let idealMultiPats = splitVar x idealMultiPat
              in trace ("split on: " ++ show x ++ " --> " ++ show idealMultiPats) $
               concatMap (\q -> algorithm (refineMultiPatSubs q a) q) idealMultiPats


refineMultiPatSubs :: MultiPattern -> [(MultiPattern, MultiPatSubst)] -> [(MultiPattern, MultiPatSubst)]
refineMultiPatSubs q = mapMaybe (\(multipat, substs) -> case unifyMultiPats q multipat of
                               Just s -> Just (multipat, s)
                               Nothing -> Nothing)

invariantHolds :: [(MultiPattern, MultiPatSubst)] -> MultiPattern -> Bool
invariantHolds multiPatsSubs idealMultiPat = all (\(a,b) -> a == b)
                                   . map (\(a,s) -> (a, applyMultiPatSubst s idealMultiPat))
                                   $ multiPatsSubs

-- splitVar should also get the type to find out how we have to split.
splitVar :: String -> MultiPattern -> [MultiPattern]
splitVar var ideal = map (\s -> applyMultiPatSubst s ideal) substs where
  substs = map (Subst var) pats
  pats = [GallinaPAppAnn "Zero" [], GallinaPAppAnn "Succ" [GallinaPVarAnn "'p" (GallinaTyCon "Nat")]]


test = refineMultiPatSubs [GallinaPAppAnn "Succ" [GallinaPVarAnn "\'p" (GallinaTyCon "Nat")],GallinaPVarAnn "\'ideal1" (GallinaTyCon "Nat")] [([GallinaPAppAnn "Zero" [],GallinaPVarAnn "x" (GallinaTyCon "Nat")],Compose IdSubst (Compose (Subst "\'ideal1" (GallinaPVarAnn "x" (GallinaTyCon "Nat"))) IdSubst))]

test1 = flip invariantHolds [GallinaPAppAnn "Succ" [GallinaPVarAnn "\'p" (GallinaTyCon "Nat")],GallinaPVarAnn "\'ideal1" (GallinaTyCon "Nat")] [([GallinaPAppAnn "Zero" [],GallinaPVarAnn "x" (GallinaTyCon "Nat")],Compose IdSubst (Compose (Subst "\'ideal1" (GallinaPVarAnn "x" (GallinaTyCon "Nat"))) IdSubst))]
