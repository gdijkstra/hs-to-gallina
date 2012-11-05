{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module BoveCapretta where

import           Control.Arrow
import           Control.Monad.State
import           Data.Map               (Map)
import qualified Data.Map               as M
import           Data.Maybe
import           Data.Set               (Set)
import qualified Data.Set               as S
import           Debug.Trace
import           Gallina.PrettyPrinting
import           Gallina.Syntax
import           Text.PrettyPrint

-- TODO: remove this, for debugging only
instance Pp MultiPattern where
  pp = hsep . map (pp . removeAnnotations)
    where
      removeAnnotations (GallinaPVarAnn var _ ) = GallinaPVar var
      removeAnnotations (GallinaPAppAnn s args) = GallinaPApp s (map removeAnnotations args)

-- We won't treat mutually recursive functions and don't care about
-- composition. If we want to use a function that has been defined
-- using B-C method, then we pretend that it's already total. The user
-- then still needs to provide the proof.
applyBoveCapretta ::  Vernacular -> Set String -> Vernacular
applyBoveCapretta v funs = trace (show funs) $ v { moduleDefinitions = newDefinitions }
  where
    specs = constrSpecsAssocs v
    tycons = tyConstrAssocs v
    newDefinitions = concatMap (tryApplyBC tycons specs funs) (moduleDefinitions v)

tryApplyBC :: TypeConstructors -> Specifications -> Set String -> GallinaDefinition -> [GallinaDefinition]
tryApplyBC tycons specs funs def = case def of
  (GallinaFixpoint [Left b]) -> apply def b (\x -> GallinaFixpoint [Left x])
  (GallinaFunction b       ) -> apply def b GallinaFunction
  _                          -> [def]
  where
    apply d b f = if (funName b) `S.member` funs
                  then [extractPredicate specs b, f (transformFunction tycons specs b)]
                  else [d]

data Specification = Spec [GallinaType] GallinaType
                   deriving Show
type Specifications = Map String Specification
-- Map type constructor names to names of their data constructors.
type TypeConstructors = Map String [String]

tyConstrAssocs :: Vernacular -> TypeConstructors
tyConstrAssocs v = M.fromList . map toTyConstrAssoc . concat
                 $ [is | (GallinaInductive is) <- moduleDefinitions v]
  where
    toTyConstrAssoc :: GallinaInductiveBody -> (String, [String])
    toTyConstrAssoc i = (inductiveName i, map constrName (inductiveConstrs i))

constrSpecsAssocs :: Vernacular -> Specifications
constrSpecsAssocs v = M.fromList . concatMap (map toSpecAssoc . inductiveConstrs) . concat
                    $ [is | (GallinaInductive is) <- moduleDefinitions v]
  where
    toSpecAssoc :: GallinaConstructor -> (String, Specification)
    toSpecAssoc c = (constrName c, constrSpec c)
    constrSpec :: GallinaConstructor -> Specification
    constrSpec c = let flat = flatTy . constrType $ c
                   in Spec (init flat) (last flat)

missingTypeMsg :: GallinaFunctionBody -> String
missingTypeMsg fun = "body of function " ++ show (funName fun) ++ " must have a type."

funSpec :: GallinaFunctionBody -> Specification
funSpec fun = Spec args res
  where
    flat = flatTy . fromMaybe (error errorMsg) . funType $ fun
    a = funArity fun
    args = take a flat
    res = fromMaybe (error errorMsg) . unflatTy . drop a $ flat
    errorMsg = "funSpec: " ++ missingTypeMsg fun

-- We need to generate a constructor for every equation of our
-- function.

extractMatches :: GallinaFunctionBody -> [GallinaMatch]
extractMatches fun = case funBody fun of
  (GallinaCase _ ms) -> ms
  _ -> error "extractPredicate: funBody is malformed."


extractPredicate :: Specifications -> GallinaFunctionBody -> GallinaDefinition
extractPredicate constrSpecAssocs fun = GallinaInductive . return $
  GallinaInductiveBody { inductiveName = predicateName fun
                       , inductiveParams = freevars funtype
                       , inductiveType = GallinaTyFun args GallinaTySet
                       , inductiveConstrs = constrs
                       }
  where
    matches = extractMatches fun
    constrs = map (uncurry (extractConstructor specs fun)) . zip matches $ [0..]
    args = argsTy (funArity fun) funtype
    errorMsg = "extractPredicate: " ++ missingTypeMsg fun
    funtype = fromMaybe (error errorMsg) . funType $ fun
    specs = M.insert (funName fun) (funSpec fun) constrSpecAssocs
    freevars (GallinaTyForall _ t) = ftv t
    freevars t = ftv t

predicateName :: GallinaFunctionBody -> String
predicateName fun = funName fun ++ "_acc"

constructorName :: GallinaFunctionBody -> Int -> String
constructorName fun i = predicateName fun ++ "_" ++ show i

extractConstructor ::
  Specifications -> GallinaFunctionBody -> GallinaMatch -> Int -> GallinaConstructor
extractConstructor specs fun match n =
  GallinaConstructor { constrName = constructorName fun n
                     , constrType = extractType specs fun match
                     }

type Context = [(String, GallinaType)]

extractType :: Specifications -> GallinaFunctionBody -> GallinaMatch -> GallinaType
extractType specs fun match = combine context recursiveCalls result
  where combine :: Context -> [GallinaType] -> GallinaType -> GallinaType
        combine ctx calls res = contextToType ctx . callsToType calls $ res
        context = extractContext specs (funSpec fun) (matchPats match)
        recursiveCalls = collectRecursiveCalls fun match
        result = resultType fun (matchPats match)
        contextToType ctx ty = foldr (\(s, t) -> GallinaTyPi s t) ty ctx
        callsToType calls ty = foldr GallinaTyFun ty calls

-- For the constructors we need to extract the context from the lhs of
-- the equation, i.e. the patterns. We need to know the types of the
-- variables bound by the patterns. This information can be extracted
-- from the specifications of the constructors.
extractContext :: Specifications -> Specification -> [GallinaPat] -> Context
extractContext specs funspec pats =
  annotatedPatsToContext (annotatePats specs funspec pats)

-- Annotate variables with their type. Wildcard case is also removed.
data GallinaPatAnnotated =
  GallinaPVarAnn String GallinaType
  | GallinaPAppAnn String [GallinaPatAnnotated]
    deriving (Show, Eq)

annotatedPatsToContext :: [GallinaPatAnnotated] -> Context
annotatedPatsToContext = concatMap f
  where f (GallinaPVarAnn s ty) = [(s, ty)]
        f (GallinaPAppAnn _ ps) = annotatedPatsToContext ps

-- Should initially be called with the specification of the function.
annotatePats :: Specifications -> Specification
                -> [GallinaPat] -> [GallinaPatAnnotated]
annotatePats specs (Spec args _) pats = zipWith ann pats args
  where
    ann :: GallinaPat -> GallinaType -> GallinaPatAnnotated
    ann (GallinaPVar s   ) ty = GallinaPVarAnn s ty
    ann (GallinaPApp c ps) ty = case M.lookup c specs of
      Nothing -> error $ "annotatePats: could not find spec of constr: " ++ show c
      Just spec -> GallinaPAppAnn c (annotatePats specs (substituteSpec spec ty) ps)
    ann GallinaPWildCard _ = error "annotatePats: Wildcards unsupported."

substituteSpec :: Specification -> GallinaType -> Specification
substituteSpec (Spec args res) ty = Spec (map subst args) (subst res)
  where
    subst = unifyTypes res ty

type TySubst = GallinaType -> GallinaType

mkTySubst :: String -> GallinaType -> TySubst
mkTySubst _ _  (GallinaTyForall _ _ ) = error "mkTySubst: tyforall not allowed."
mkTySubst a ty (GallinaTyFun l r    ) = GallinaTyFun (mkTySubst a ty l) (mkTySubst a ty r)
mkTySubst a ty (GallinaTyApp l r    ) = GallinaTyApp (mkTySubst a ty l) (mkTySubst a ty r)
mkTySubst a ty (GallinaTyVar s      ) = if a == s then ty else GallinaTyVar s
mkTySubst _ _  (GallinaTyCon c      ) = GallinaTyCon c
mkTySubst _ _  GallinaTySet           = GallinaTySet
mkTySubst _ _  (GallinaTyPi _ _ _   ) = error "mkTySubst: typi not allowed."

-- left type should be more general than right type.
unifyTypes :: GallinaType -> GallinaType -> TySubst
unifyTypes (GallinaTyApp p q) (GallinaTyApp r s) = unifyTypes p r . unifyTypes q s
unifyTypes (GallinaTyCon s1 ) (GallinaTyCon s2 ) = if s1 /= s2
                                              then error "unifyTypes: impossible happened"
                                              else id
unifyTypes (GallinaTyVar a)   r                  = mkTySubst a r
unifyTypes l                  r                  =
  error $ "unifyTypes: unsupported: " ++ show l ++ " ~> " ++ show r

-- Collection of recursive calls.
collectRecursiveCalls :: GallinaFunctionBody -> GallinaMatch -> [GallinaType]
collectRecursiveCalls fun match = map (callToType . snd)
                                  . filter isRecursive
                                  . collectArgs . matchTerm
                                  $ match
  where
    callToType :: [GallinaTerm] -> GallinaType
    callToType ts = termsToType ts (GallinaTyCon (predicateName fun))
    isRecursive :: (String, [GallinaTerm]) -> Bool
    isRecursive = (== funName fun) . fst

termsToType :: [GallinaTerm] -> GallinaType -> GallinaType
termsToType ts ty = foldl GallinaTyApp ty . map termToType $ ts

termToType :: GallinaTerm -> GallinaType
termToType (GallinaVar s  ) = GallinaTyVar s
termToType (GallinaApp l r) = GallinaTyApp (termToType l) (termToType r)
termToType _                = error "termToType: only var and app supported."

collectArgs :: GallinaTerm -> [(String, [GallinaTerm])]
collectArgs t = collectArgs' t True []
  where
    collectArgs' :: GallinaTerm -> Bool -> [GallinaTerm] -> [(String, [GallinaTerm])]
    collectArgs' (GallinaVar s  ) l args = if l
                                           then [(s, reverse args)]
                                           else []
    collectArgs' (GallinaApp l r) _ args = collectArgs' l True (args ++ [r])
                                           ++ collectArgs' r False []
    collectArgs' _                _ _    = error "collectArgs: only var and app supported"


-- The result of the constructor should be the predicate applied to
-- the pattern found in the lhs of the equation.
resultType :: GallinaFunctionBody -> [GallinaPat] -> GallinaType
resultType _   []   = error "resultType: pats list should never be empty"
resultType fun pats = GallinaTyApp (GallinaTyCon (predicateName fun))
                      $ foldr1 GallinaTyApp (map patternToType pats)

patternToType :: GallinaPat -> GallinaType
patternToType (GallinaPVar s    ) = GallinaTyVar s
patternToType (GallinaPApp s ps ) = foldl GallinaTyApp (GallinaTyCon s)
                                    . map patternToType $ ps
patternToType GallinaPWildCard    = error "patternToType: wildcards are not supported"

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
---------------------------------------------------------------------------------

transformFunction :: TypeConstructors -> Specifications -> GallinaFunctionBody -> GallinaFunctionBody
transformFunction tycons specs fun = trace ("missing:" ++ show (map pp $ missingPats tycons specs fun))
                                     $ addPredArgument . addMissingPatterns tycons specs $ fun


-- We add the accessability predicate as an extra argument to the
-- function.
addPredArgument :: GallinaFunctionBody -> GallinaFunctionBody
addPredArgument fun = fun { funType = newTy, funArity = newArity }
  where
    (Spec args res) = funSpec fun
    predicate = GallinaTyApp (GallinaTyCon (predicateName fun))
                $ foldr1 GallinaTyApp (map (\n -> GallinaTyVar ('x':show n)) [0 .. (funArity fun - 1)])
    newTy = unflatTy (args ++ [predicate, res])
    newArity = funArity fun + 1

addMissingPatterns :: TypeConstructors -> Specifications -> GallinaFunctionBody -> GallinaFunctionBody
addMissingPatterns tycons specs fun = fun { funBody = newBody }
  where
    missingMatches = undefined
    returnTy = undefined
    newBody = case funBody fun of
      GallinaCase ts ms -> GallinaApp
                           (GallinaDepCase (zipWith (\term n -> (term, "'y" ++ show n)) ts ([0..] :: [Int])) returnTy (ms ++ missingMatches))
                           undefined
      _ -> error "addMissingPatterns: malformed function body"

-- Missing patterns stuff.
type MultiPattern = [GallinaPatAnnotated]

missingPats :: TypeConstructors -> Specifications -> GallinaFunctionBody -> [MultiPattern]
missingPats tycons specs fun = evalState (algorithm tycons specs initialPatSubs (initialIdealMultiPat (funSpec fun))) 0
   where
     pats = map (annotatePats specs (funSpec fun) . matchPats) (extractMatches fun)
     initialPatSubs = zipWith (\p q -> (p, fromJust (unifyMultiPats q p)))
                      pats
                      (repeat (initialIdealMultiPat (funSpec fun)))

initialIdealMultiPat :: Specification -> MultiPattern
initialIdealMultiPat (Spec args _) = zipWith (\ty n -> GallinaPVarAnn ("'q" ++ show n) ty) args ([0..] :: [Int])

data MultiPatSubst =
  Compose MultiPatSubst MultiPatSubst
  | Subst String GallinaType GallinaPatAnnotated
  | IdSubst
    deriving Show

-- We assume that length ps0 == length ps1, i.e. no malformed pats.
unifyMultiPats :: MultiPattern -> MultiPattern -> Maybe MultiPatSubst
unifyMultiPats l r = fmap (foldr Compose IdSubst)
                     $ sequence
                     $ zipWith unifyPatAnn l r

-- We assume that the patterns are linear, i.e. every variable in the
-- multipattern occurs exactly once.
unifyPatAnn :: GallinaPatAnnotated -> GallinaPatAnnotated -> Maybe MultiPatSubst
unifyPatAnn (GallinaPVarAnn v t   ) p = Just $ Subst v t p
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
applyPatSubst (Subst var _ pat) = applySubst var pat
  where
    applySubst v0 pat0 pat1@(GallinaPVarAnn v1 _  ) = if v0 == v1 then pat0 else pat1
    applySubst v0 pat0 (GallinaPAppAnn constr pats) = GallinaPAppAnn constr
                                                      . map (applySubst v0 pat0)
                                                      $ pats

-- Returns Nothing if the substs only rename variables to variables.
-- Return Just x where x is a variable mapped to a non-variable.
hasNonRenaming :: MultiPatSubst -> Maybe (String, GallinaType)
hasNonRenaming IdSubst                          = Nothing
hasNonRenaming (Subst s t (GallinaPAppAnn _ _)) = Just (s, t)
hasNonRenaming (Subst _ _ (GallinaPVarAnn _ _)) = Nothing
hasNonRenaming (Compose l r                   ) = hasNonRenaming l
                                                  `mplus` hasNonRenaming r

algorithm :: TypeConstructors -> Specifications -> [(MultiPattern, MultiPatSubst)] -> MultiPattern -> State Int [MultiPattern]
algorithm _ _ []       idealMultiPat = return [idealMultiPat]
algorithm tycons specs a@((_, s1):_) idealMultiPat =
  case hasNonRenaming s1 of
    Nothing -> if length a == 1 then return [] else error "algorithm: overlap"
    Just (x, ty) -> do
      n <- get
      let idealMultiPats = splitVar tycons specs ty n x idealMultiPat
      modify (+1)
      fmap concat . mapM (\q -> algorithm tycons specs (refineMultiPatSubs q a) q) $ idealMultiPats

refineMultiPatSubs :: MultiPattern -> [(MultiPattern, MultiPatSubst)] -> [(MultiPattern, MultiPatSubst)]
refineMultiPatSubs q = mapMaybe (\(multipat, _) -> fmap (\s -> (multipat, s)) $ unifyMultiPats q multipat)

invariantHolds :: [(MultiPattern, MultiPatSubst)] -> MultiPattern -> Bool
invariantHolds multiPatsSubs idealMultiPat = all (\(a,b) -> a == b)
                                             . map (\(a,s) -> (a, applyMultiPatSubst s idealMultiPat))
                                             $ multiPatsSubs

getTypeConstr :: GallinaType -> String
getTypeConstr (GallinaTyApp l _    ) = getTypeConstr l
getTypeConstr (GallinaTyCon c      ) = c
getTypeConstr (GallinaTyForall _ _ ) = error "getTypeConstr: foralls not supported."
getTypeConstr (GallinaTyFun _ _    ) = error "getTypeConstr: function types not supported."
getTypeConstr (GallinaTyVar _      ) = error "getTypeConstr: type var not supported."
getTypeConstr GallinaTySet           = error "getTypeConstr: set type not supported."
getTypeConstr (GallinaTyPi _ _ _   ) = error "getTypeConstr: pi types not supported."

maybeTuple :: (a, Maybe b) -> Maybe (a, b)
maybeTuple (_, Nothing) = Nothing
maybeTuple (a, Just b ) = return (a, b)

-- splitVar should also get the type to find out how we have to split.
splitVar :: TypeConstructors -> Specifications -> GallinaType -> Int -> String -> MultiPattern -> [MultiPattern]
splitVar tycons specs ty n var ideal = map (\s -> applyMultiPatSubst s ideal) substs where
  substs = map (Subst var ty) pats
  -- pats = [GallinaPAppAnn "Zero" [], GallinaPAppAnn "Succ" [GallinaPVarAnn varName (GallinaTyCon "Nat")]]
  pats = fromJust $ do
    constrNames <- M.lookup (getTypeConstr ty) tycons
    constrSpecs <- mapM (\v -> maybeTuple (v, M.lookup v specs)) constrNames
    let actualSpecs = map (second (flip substituteSpec ty)) constrSpecs
    return . map (uncurry mkPat) $ actualSpecs

  mkPat c (Spec args _) = GallinaPAppAnn c $ zipWith (\t m -> GallinaPVarAnn ("'p" ++ show n ++ "x" ++ show m) t) args ([0..] :: [Int])

--
