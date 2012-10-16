module BoveCapretta where

import           Data.Map       (Map)
import qualified Data.Map       as M
import           Data.Maybe
import           Data.Set       (Set)
import qualified Data.Set       as S
import           Gallina.Syntax

-- We won't treat mutually recursive functions and don't care about
-- composition. If we want to use a function that has been defined
-- using B-C method, then we pretend that it's already total. The user
-- then still needs to provide the proof.

applyBoveCapretta :: Set String -> Vernacular -> Vernacular
applyBoveCapretta funs v = undefined

data Specification = Spec [GallinaType] GallinaType
                   deriving Show

type Context = [(String, GallinaType)]

constrSpecsAssocs :: Vernacular -> Map String Specification
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

extractPredicate :: Map String Specification -> GallinaFunctionBody -> GallinaInductiveBody
extractPredicate constrSpecAssocs fun =
  GallinaInductiveBody { inductiveName = funName fun ++ "Acc"
                       , inductiveParams = freevars funtype
                       , inductiveType = GallinaTyFun args GallinaTySet
                       , inductiveConstrs = undefined
                       }
  where
    args = argsTy (funArity fun) funtype
    errorMsg = "extractPredicate: " ++ missingTypeMsg fun
    funtype = fromMaybe (error errorMsg) . funType $ fun
    specAssocs = M.insert (funName fun) (funSpec fun) constrSpecAssocs
    freevars (GallinaTyForall _ t) = ftv t
    freevars t = ftv t

-- Annotate variables with their type. Wildcard case is also removed.
data GallinaPatAnnotated =
  GallinaPVarAnn String GallinaType
  | GallinaPAppAnn String [GallinaPatAnnotated]

-- Should initially be called with the specification of the function.
annotatePats :: Map String Specification -> Specification
                -> [GallinaPat] -> [GallinaPatAnnotated]
annotatePats constrSpecAssocs (Spec args _) pats = zipWith ann pats args
  where
    ann :: GallinaPat -> GallinaType -> GallinaPatAnnotated
    ann (GallinaPVar s   ) ty = GallinaPVarAnn s ty
    ann (GallinaPApp c ps) ty = case M.lookup c constrSpecAssocs of
      Nothing -> error $ "annotatePats: could not find spec of constr: " ++ show c
      Just spec -> GallinaPAppAnn c (annotatePats constrSpecAssocs spec ps)
    ann GallinaPWildCard _ = error "annotatePats: Wildcards unsupported."

annotatedPatsToContext :: [GallinaPatAnnotated] -> Context
annotatedPatsToContext = concatMap f
  where f (GallinaPVarAnn s ty) = [(s, ty)]
        f (GallinaPAppAnn _ ps) = annotatedPatsToContext ps

extractContexts :: Map String Specification -> GallinaFunctionBody -> [Context]
extractContexts constrSpecAssocs fun = case funBody fun of
  GallinaCase _ ms -> map (\pats -> annotatedPatsToContext (annotatePats constrSpecAssocs (funSpec fun) pats)) (map matchPats ms)
  _ -> error "extractContexts: Should not happen"

-- test stuff

testSpecs = constrSpecsAssocs testProgram

testExtract = extractContexts testSpecs (GallinaFunctionBody {funArity = 1, funName = "log", funType = Just (GallinaTyFun (GallinaTyCon "Nat") (GallinaTyCon "Nat")), funBody = GallinaCase [GallinaVar "x0"] [GallinaMatch {matchPats = [GallinaPApp "Succ" [GallinaPApp "Zero" []]], matchTerm = GallinaVar "Zero"},GallinaMatch {matchPats = [GallinaPApp "Succ" [GallinaPApp "Succ" [GallinaPVar "p"]]], matchTerm = GallinaApp (GallinaVar "Succ") (GallinaApp (GallinaVar "log") (GallinaApp (GallinaVar "Succ") (GallinaApp (GallinaVar "div2") (GallinaVar "p"))))}]})

testProgram = Vernacular {moduleName = "BCExample", moduleDefinitions = [GallinaInductive [GallinaInductiveBody {inductiveName = "Nat", inductiveParams = [], inductiveType = GallinaTySet, inductiveConstrs = [GallinaConstructor {constrName = "Zero", constrType = GallinaTyCon "Nat"},GallinaConstructor {constrName = "Succ", constrType = GallinaTyFun (GallinaTyCon "Nat") (GallinaTyCon "Nat")}]}],GallinaFixpoint [Left (GallinaFunctionBody {funArity = 1, funName = "div2", funType = Just (GallinaTyFun (GallinaTyCon "Nat") (GallinaTyCon "Nat")), funBody = GallinaCase [GallinaVar "x0"] [GallinaMatch {matchPats = [GallinaPApp "Zero" []], matchTerm = GallinaVar "Zero"},GallinaMatch {matchPats = [GallinaPApp "Succ" [GallinaPApp "Zero" []]], matchTerm = GallinaVar "Zero"},GallinaMatch {matchPats = [GallinaPApp "Succ" [GallinaPApp "Succ" [GallinaPVar "n"]]], matchTerm = GallinaApp (GallinaVar "Succ") (GallinaApp (GallinaVar "div2") (GallinaVar "n"))}]})],GallinaFixpoint [Left (GallinaFunctionBody {funArity = 1, funName = "log", funType = Just (GallinaTyFun (GallinaTyCon "Nat") (GallinaTyCon "Nat")), funBody = GallinaCase [GallinaVar "x0"] [GallinaMatch {matchPats = [GallinaPApp "Succ" [GallinaPApp "Zero" []]], matchTerm = GallinaVar "Zero"},GallinaMatch {matchPats = [GallinaPApp "Succ" [GallinaPApp "Succ" [GallinaPVar "p"]]], matchTerm = GallinaApp (GallinaVar "Succ") (GallinaApp (GallinaVar "log") (GallinaApp (GallinaVar "Succ") (GallinaApp (GallinaVar "div2") (GallinaVar "p"))))}]})]]}
