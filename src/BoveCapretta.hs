module BoveCapretta where

import           Data.Map       (Map)
import qualified Data.Map       as M
import           Data.Maybe
import           Data.Set       (Set)
import qualified Data.Set       as S
import           Debug.Trace
--import           Gallina.PrettyPrinting
import           Gallina.Syntax
--import           Text.PrettyPrint

-- We won't treat mutually recursive functions and don't care about
-- composition. If we want to use a function that has been defined
-- using B-C method, then we pretend that it's already total. The user
-- then still needs to provide the proof.
applyBoveCapretta ::  Vernacular -> Set String -> Vernacular
applyBoveCapretta v funs = trace (show funs) $ v { moduleDefinitions = newDefinitions }
  where
    specsAssocs = constrSpecsAssocs v
    newDefinitions = concatMap transform (moduleDefinitions v)
    transform d@(GallinaFixpoint [Left b]) = if (funName b) `S.member` funs
                                      then [extractPredicate specsAssocs b, d]
                                      else [d]
    transform d = [d]

data Specification = Spec [GallinaType] GallinaType
                   deriving Show
type Specifications = Map String Specification

constrSpecsAssocs :: Vernacular -> Specifications
constrSpecsAssocs = M.fromList . concatMap (map toSpecAssoc . inductiveConstrs)
                    . filterInd . moduleDefinitions
  where
    filterInd :: [GallinaDefinition] -> [GallinaInductiveBody]
    filterInd = concatMap f
      where f (GallinaInductive is) = is
            f _ = []
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

extractPredicate :: Specifications -> GallinaFunctionBody -> GallinaDefinition
extractPredicate constrSpecAssocs fun = GallinaInductive . return $
  GallinaInductiveBody { inductiveName = predicateName fun
                       , inductiveParams = freevars funtype
                       , inductiveType = GallinaTyFun args GallinaTySet
                       , inductiveConstrs = constrs
                       }
  where
    matches = case funBody fun of
      (GallinaCase _ ms) -> ms
      _ -> error "extractPredicate: funBody is malformed."
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
    subst = unify res ty

type Subst = GallinaType -> GallinaType

mkSubst :: String -> GallinaType -> Subst
mkSubst _ _  (GallinaTyForall _ _ ) = error "mkSubst: tyforall not allowed."
mkSubst a ty (GallinaTyFun l r    ) = GallinaTyFun (mkSubst a ty l) (mkSubst a ty r)
mkSubst a ty (GallinaTyApp l r    ) = GallinaTyApp (mkSubst a ty l) (mkSubst a ty r)
mkSubst a ty (GallinaTyVar s      ) = if a == s then ty else GallinaTyVar s
mkSubst _ _  (GallinaTyCon c      ) = GallinaTyCon c
mkSubst _ _  GallinaTySet           = GallinaTySet
mkSubst _ _  (GallinaTyPi _ _ _   ) = error "mkSubst: typi not allowed."

-- left type should be more general than right type.
unify :: GallinaType -> GallinaType -> Subst
unify (GallinaTyApp p q) (GallinaTyApp r s) = unify p r . unify q s
unify (GallinaTyCon s1 ) (GallinaTyCon s2 ) = if s1 /= s2
                                              then error "mkSubst: impossible happened"
                                              else id
unify (GallinaTyVar a)   r                  = mkSubst a r
unify l                  r                  =
  error $ "mkSubst: unsupported: " ++ show l ++ " ~> " ++ show r

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
    collectArgs' (GallinaVar s  ) left args = if left
                                              then [(s, reverse args)]
                                              else []
    collectArgs' (GallinaApp l r) _    args = collectArgs' l True (args ++ [r])
                                              ++ collectArgs' r False []
    collectArgs' _                _    _    = error "collectArgs: only var and app supported"


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

