module BoveCapretta where

import           AG
import           Control.Arrow       (second)
import           Control.Monad.State (State, evalState, get, modify, mplus)
import qualified Data.List           as L
import           Data.Map            (Map)
import qualified Data.Map            as M
import           Data.Maybe          (fromJust, fromMaybe, mapMaybe)
import           Data.Set            (Set)
import qualified Data.Set            as S
import           Debug.Trace         (trace)
import           Gallina.Syntax

-- | Specification of a data constructor/function: the types of its
-- arguments and the resulting type.
data Specification = Spec [GallinaType] GallinaType
                   deriving Show

-- | Mapping from data constructor name to its specification.
type Specifications = Map String Specification

-- | Mapping from type constructor name to the names of its data
-- constructors.
type TypeConstructors = Map String [String]

-- | Apply the Bove-Capretta method to the definitions as specified in
-- the pragmas.
applyBoveCapretta ::  Result -> Result
applyBoveCapretta r = r { resVernacular = v { documentCommands = newDefinitions } }
  where
    funs = bcDefinitions r
    v = resVernacular r
    newDefinitions = concatMap (tryApplyBC tycons specs funs) (documentCommands . resVernacular $ r)

    tycons :: TypeConstructors
    tycons = M.fromList . (listTyConstrAssoc :) . map toTyConstrAssoc . concat
                 $ [is | (GallinaInductive is _) <- documentCommands v]
      where
        listTyConstrAssoc = ("list", ["nil", "cons"])
        toTyConstrAssoc :: GallinaInductiveBody -> (String, [String])
        toTyConstrAssoc i = (inductiveName i, map constrName (inductiveConstrs i))

    specs :: Specifications
    specs = M.fromList . (listAssocs ++) . concatMap (map toSpecAssoc . inductiveConstrs) . concat
                    $ [is | (GallinaInductive is _) <- documentCommands v]
      where
        listAssocs :: [(String,Specification)]
        listAssocs = [ ("nil", Spec [] (GallinaTyList (GallinaTyVar "a")))
                     , ("cons", Spec [GallinaTyVar "a", GallinaTyList (GallinaTyVar "a")] (GallinaTyList (GallinaTyVar "a")))
                     ]
        toSpecAssoc :: GallinaConstructor -> (String, Specification)
        toSpecAssoc c = (constrName c, constrSpec c)
        constrSpec :: GallinaConstructor -> Specification
        constrSpec c = let flat = flatTy . constrType $ c
                       in Spec (init flat) (last flat)

-- | Try to apply the Bove-Capretta method to a definition, given the
-- information about type and data constructors and which definitions
-- we want to apply this method to. It will only apply the method to
-- the definition if it is a function definition (not necessarily
-- recursive). If it is a mutually recursive definition, then we will
-- ignore, as we cannot deal with those definitions in Coq.
tryApplyBC :: TypeConstructors -> Specifications -> Set String -> VernacularCommand -> [VernacularCommand]
tryApplyBC tycons specs funs def = case def of
  (GallinaFixpoint [Left b] c) -> apply def b (\x -> GallinaFixpoint [Left x] c)
  (GallinaFunction b         ) -> apply def b GallinaFunction
  _                            -> [def]
  where
    apply d b f = if (funName b) `S.member` funs
                  then concat [ [extractPredicate specs b]
                              , extractNonTheorems tycons specs b
                              , extractInvTheorems specs b
                              , [f (transformFunction tycons specs b)]
                              ]
                  else [d]


-- | Error message to display when we cannot find the type of a
-- function definition.
missingTypeMsg :: GallinaFunctionBody -> String
missingTypeMsg fun = "body of function " ++ show (funName fun) ++ " must have a type."

-- | Extract the specification from a function definition. Will yield
-- an error if the definition is not typed, i.e. @funType fun ==
-- Nothing@.
funSpec :: GallinaFunctionBody -> Specification
funSpec fun = Spec args res
  where
    flat = flatTy . fromMaybe (error errorMsg) . funType $ fun
    a = funArity fun
    args = take a flat
    res = fromMaybe (error errorMsg) . unflatTy . drop a $ flat
    errorMsg = "funSpec: " ++ missingTypeMsg fun

-- | Extract the matches from a function body. Note that this can fail
-- if the function body is malformed for some strange reason.
extractMatches :: GallinaFunctionBody -> [GallinaMatch]
extractMatches fun = case funBody fun of
  (GallinaCase _ ms) -> ms
  _ -> error "extractPredicate: funBody is malformed."

-- | Extract the Bove-Capretta data type from a function definition.
extractPredicate :: Specifications -> GallinaFunctionBody -> VernacularCommand
extractPredicate specs fun = GallinaInductive
  [GallinaInductiveBody { inductiveName = predicateName fun
                        , inductiveParams = freevars funtype
                        , inductiveType = fromJust . unflatTy $ args ++ [GallinaTyProp]
                        , inductiveConstrs = constrs
                        }
  ]
  False -- This data type is not coinductive.
  where
    matches = extractMatches fun
    constrs = map (uncurry (extractConstructor specs fun)) . zip matches $ [0..]
    (args, _) = argsResTy (funArity fun) (fromJust . funType $ fun)
    errorMsg = "extractPredicate: " ++ missingTypeMsg fun
    funtype = fromMaybe (error errorMsg) . funType $ fun

-- | Free variables of a type, ignoring the outermost
-- 'GallinaTyForall'.
freevars :: GallinaType -> [String]
freevars (GallinaTyForall _ t) = ftv t
freevars t = ftv t

-- | Generate the name of the Bove-Capretta predicate of the given
-- function.
predicateName :: GallinaFunctionBody -> String
predicateName fun = funName fun ++ "_acc"

-- | Generate the n-th constructor of the Bove-Capretta predicate of
-- the given function definition.
extractConstructor ::
  Specifications -> GallinaFunctionBody -> GallinaMatch -> Int -> GallinaConstructor
extractConstructor specs fun match n =
  GallinaConstructor { constrName = predicateName fun ++ "_" ++ show n
                     , constrType = extractType specs fun match
                     }

-- | A context is a list of type variables with their types.
type Context = [(String, GallinaType)]

-- | Extract the type of the constructor of the Bove-Capretta
-- predicate corresponding to the given 'GallinaMatch'.
extractType :: Specifications -> GallinaFunctionBody -> GallinaMatch -> GallinaType
extractType specs fun match = combine context recursiveCalls result
  where combine :: Context -> [GallinaType] -> GallinaType -> GallinaType
        combine ctx calls res = contextToType ctx . callsToType calls $ res
        context = extractContext specs (funSpec fun) (matchPats match)
        recursiveCalls = collectRecursiveCalls fun match
        result = resultType fun (matchPats match)
        contextToType ctx ty = if (not (null ctx)) then GallinaTyPi ctx ty else ty
        callsToType calls ty = fromJust . unflatTy $ calls ++ [ty]

-- | Extract the context (type variables and their types) induces by
-- the multipattern of an equation.
extractContext :: Specifications -> Specification -> [GallinaPat] -> Context
extractContext specs funspec = concat . extractContexts specs funspec

-- | Extract the contexts, for every 'GallinaPat' we generate a
-- context, which might be empty.
extractContexts :: Specifications -> Specification -> [GallinaPat] -> [Context]
extractContexts specs funspec pats =
  annotatedPatsToContexts (annotatePats specs funspec pats)

-- | Annotate variables with their type. Note that this is a
-- restricted pattern syntax. Wildcard cases are removed, since we
-- then would need to make up names during the generation of the
-- Bove-Capretta predicate.
data GallinaPatAnnotated =
  GallinaPVarAnn String GallinaType
  | GallinaPAppAnn String MultiPattern
  | GallinaPTupleAnn MultiPattern
    deriving (Show, Eq)

-- | Annotate a multipattern, given the specifications of the data
-- constructors and the specification of the function to which the
-- multipattern belongs to.
annotatePats :: Specifications -> Specification
                -> [GallinaPat] -> MultiPattern
annotatePats specs (Spec args _) pats = zipWith ann pats args
  where
    ann :: GallinaPat -> GallinaType -> GallinaPatAnnotated
    ann (GallinaPTuple s ) (GallinaTyTuple tys) = GallinaPTupleAnn $ zipWith ann s tys
    ann (GallinaPVar s   ) ty = GallinaPVarAnn s ty
    ann (GallinaPApp c ps) ty = case M.lookup c specs of
      Nothing -> error $ "annotatePats: could not find spec of constr: " ++ show c
      Just spec -> GallinaPAppAnn c (annotatePats specs (substituteSpec spec ty) ps)
    ann GallinaPWildCard _ = error "annotatePats: Wildcards unsupported."
    ann _ _ = error "annotatePats: pattern is not well-typed."

-- | Remove the type annotations from a multipattern.
removeAnnotations :: MultiPattern -> [GallinaPat]
removeAnnotations = map removeAnnotations'
  where
    removeAnnotations' (GallinaPVarAnn var _ ) = GallinaPVar var
    removeAnnotations' (GallinaPAppAnn s args) = GallinaPApp s (map removeAnnotations' args)
    removeAnnotations' (GallinaPTupleAnn s   ) = GallinaPTuple (map removeAnnotations' s)

-- | Extract the contexts out of an annotated multipattern.
annotatedPatsToContexts :: MultiPattern -> [Context]
annotatedPatsToContexts = map f
  where f (GallinaPVarAnn s ty) = [(s, ty)]
        f (GallinaPAppAnn _ ps) = concat $ annotatedPatsToContexts ps
        f (GallinaPTupleAnn ps) = concat $ annotatedPatsToContexts ps


-- | Try to unify the result type of the 'Specification' with the
-- given 'GallinaType' and apply this substitution to the
-- 'Specification'. We need this when dealing with data types that
-- have type parameters.
substituteSpec :: Specification -> GallinaType -> Specification
substituteSpec (Spec args res) ty = Spec (map subst args) (subst res)
  where
    subst = case unifyTypes res ty of
      Left  err -> error ("substituteSpec: " ++ err)
      Right sub -> sub

-- | Try to unify the left type with the right one. Expects the left
-- type to be the more general type. Note that it will crash if the
-- types cannot be unified.
unifyTypes :: GallinaType -> GallinaType -> Either String TySubst
unifyTypes (GallinaTyApp p q) (GallinaTyApp r s) = do
  s0 <- unifyTypes q s
  s1 <- unifyTypes p r
  return (s1 . s0)
unifyTypes (GallinaTyCon s1 ) (GallinaTyCon s2 ) =
  if s1 /= s2
  then Left ("unifyTypes: could not unify " ++ show s1 ++ " with " ++ show s2 ++ ".")
  else Right id
unifyTypes (GallinaTyVar a)   r                  =
  Right (mkTySubst a r)
unifyTypes (GallinaTyList a)  (GallinaTyList b ) =
  unifyTypes a b
unifyTypes l                  r                  =
  Left ("unifyTypes: unsupported: " ++ show l ++ " ~> " ++ show r ++ ".")

-- | Type substitution.
type TySubst = GallinaType -> GallinaType

-- | Make a type substitution substituting the given variable with the
-- given 'GallinaType. Note that trying to perform a substitution on a
-- 'GallinaTyForall', 'GallinaTyPi' or 'GallinaTyTerm' will yield an
-- error.
mkTySubst :: String -> GallinaType -> TySubst
mkTySubst a ty (GallinaTyTuple ts   ) = GallinaTyTuple (map (mkTySubst a ty) ts)
mkTySubst a ty (GallinaTyFun l r    ) = GallinaTyFun (mkTySubst a ty l) (mkTySubst a ty r)
mkTySubst a ty (GallinaTyApp l r    ) = GallinaTyApp (mkTySubst a ty l) (mkTySubst a ty r)
mkTySubst a ty (GallinaTyVar s      ) = if a == s then ty else GallinaTyVar s
mkTySubst a ty (GallinaTyList t     ) = GallinaTyList (mkTySubst a ty t)
mkTySubst a ty (GallinaTyEq l r     ) = GallinaTyEq (mkTySubst a ty l) (mkTySubst a ty r)
mkTySubst _ _  (GallinaTyCon c      ) = GallinaTyCon c
mkTySubst _ _  GallinaTySet           = GallinaTySet
mkTySubst _ _  GallinaTyProp          = GallinaTyProp
mkTySubst _ _  (GallinaTyTerm _     ) = error "mkTySubst: terms should not occur here."
mkTySubst _ _  (GallinaTyForall _ _ ) = error "mkTySubst: foralls should not occur here."
mkTySubst _ _  (GallinaTyPi _ _     ) = error "mkTySubst: typi should not occur here."

-- | Collect the recursive calls in a match, from left to
-- right. Returns a list of types, so that they can be used to create
-- the constructor of the corresponding Bove-Capretta predicate.
collectRecursiveCalls :: GallinaFunctionBody -> GallinaMatch -> [GallinaType]
collectRecursiveCalls fun match = map (callToType . snd)
                                  . filter isRecursive
                                  . collectArgs . matchTerm
                                  $ match
  where
    callToType :: [GallinaTerm] -> GallinaType
    callToType = GallinaTyTerm . foldl GallinaApp (GallinaVar (predicateName fun))
    isRecursive :: (String, [GallinaTerm]) -> Bool
    isRecursive = (== funName fun) . fst

-- | Collect all the applications: associate the function being called
-- with all its arguments.
collectArgs :: GallinaTerm -> [(String, [GallinaTerm])]
collectArgs t = collectArgs' t False []
  where
    collectArgs' :: GallinaTerm -> Bool -> [GallinaTerm] -> [(String, [GallinaTerm])]
    collectArgs' (GallinaVar s  ) l args = if l
                                           then [(s, reverse args)]
                                           else []
    collectArgs' (GallinaList ts) l _    = if l
                                           then error "collectArgs: term does not type check."
                                           else concatMap (\x -> collectArgs' x False []) ts
    collectArgs' (GallinaApp l r) _ args = collectArgs' l True (args ++ [r])
                                           ++ collectArgs' r False []
    collectArgs' _                _ _    = error "collectArgs: only var and app supported"

-- | Create the result type of a constructor of the Bove-Capretta
-- predicate we are currently defining. The result of the constructor
-- should be the predicate applied to the pattern found in the lhs of
-- the equation.
resultType :: GallinaFunctionBody -> [GallinaPat] -> GallinaType
resultType _   []   = error "resultType: pats list should never be empty"
resultType fun pats = foldl1 GallinaTyApp $ GallinaTyCon (predicateName fun) : map patternToType pats

-- | Convert a pattern to a type. Will crash on wildcards as we do not
-- support those.
patternToType :: GallinaPat -> GallinaType
patternToType (GallinaPTuple ps ) = GallinaTyTuple . map patternToType $ ps
patternToType (GallinaPVar s    ) = GallinaTyVar s
patternToType (GallinaPApp s ps ) = foldl GallinaTyApp (GallinaTyCon s)
                                    . map patternToType $ ps
patternToType GallinaPWildCard    = error "patternToType: wildcards are not supported"

----

-- | Extract the non theorems and their proofs, i.e. the theorems that
-- tell us that the missing patterns of a function definition are
-- indeed missing.
extractNonTheorems :: TypeConstructors -> Specifications -> GallinaFunctionBody -> [VernacularCommand]
extractNonTheorems tycons specs fun  = zipWith mkTheorem multipats ([0 ..] :: [Int])
  where
    arity = funArity fun
    multipats = missingPats tycons specs fun
    params = map (\v -> (v, GallinaTySet)) . foldr L.union [] . map freevars $ argTys
    context multipat = extractContext specs (funSpec fun) multipat
    predArg = foldl GallinaTyApp (GallinaTyCon (predicateName fun)) $ map GallinaTyVar (map fst args)
    argTys = case funSpec fun of Spec a _ -> a
    args = zipWith (\n t -> ("x" ++ show n, t)) [0 .. arity - 1] argTys
    ty multipat = foldr GallinaTyFun (GallinaTyCon "Logic.False")
                  $ predArg : zipWith (\p n -> GallinaTyEq (GallinaTyVar ('x':show n)) (patternToType p)) multipat [0 .. arity - 1]

    mkTheorem multipat n = GallinaThmDef $ GallinaTheorem
                      { theoremName = funName fun ++ "_acc_non_" ++ show n
                      , theoremProp = GallinaTyPi (params ++ args ++ context (removeAnnotations multipat)) (ty (removeAnnotations multipat))

                      , theoremProof = "intros " ++ unwords (map fst (params ++ args ++ context (removeAnnotations multipat)))
                                       ++ " H; case H; intros; discriminate."
                      }


---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
---------------------------------------------------------------------------------

-- | Add the appropriate inversion theorem to every recursive call and
-- add calls to the non theorems for the missing pattern matches.
transformFunction :: TypeConstructors -> Specifications -> GallinaFunctionBody -> GallinaFunctionBody
transformFunction tycons specs fun = addPredArgument . addMissingPatterns tycons specs $ fun


-- | We add the accessability predicate as an extra argument to the
-- function type and increase the arity.
addPredArgument :: GallinaFunctionBody -> GallinaFunctionBody
addPredArgument fun = fun { funType = newTy, funArity = newArity }
  where
    (Spec args res) = funSpec fun
    predicate = foldl1 GallinaTyApp $ (GallinaTyCon (predicateName fun)) : map (\n -> GallinaTyVar ('x':show n)) [0 .. (funArity fun - 1)]
    newTy = case (funType fun) of
      (Just (GallinaTyForall vars _)) -> Just $ GallinaTyForall vars (fromJust $ unflatTy (args ++ [predicate, res]))
      _ -> unflatTy (args ++ [predicate, res])
    newArity = funArity fun + 1

-- | We add the missing pattern matches with calls to the non
-- theorems.
addMissingPatterns :: TypeConstructors -> Specifications -> GallinaFunctionBody -> GallinaFunctionBody
addMissingPatterns tycons specs fun = fun { funBody = newBody }
  where
    arity = funArity fun
    (_, resultTy) = argsResTy arity (fromJust $ funType fun)
    name = funName fun
    missingMatches = mkMissingMatches arity name resultTy (missingPats tycons specs fun)
    returnTy = foldr1 GallinaTyFun
               $ map (\n -> GallinaTyEq (GallinaTyVar ('x':show n)) (GallinaTyVar ("_y" ++ show n))) [0 .. arity - 1]
               ++ [resultTy]
    newBody = case funBody fun of
      GallinaCase ts _ -> foldl1 GallinaApp (
                           (GallinaDepCase (zipWith (\term n -> (term, "_y" ++ show n)) ts ([0..] :: [Int]))
                            returnTy
                            (adjustExistingMatches fun ++ missingMatches))
                           : map (\n -> GallinaApp (GallinaVar "refl_equal") (GallinaVar ('x':show n))) [0 .. arity - 1])
      _ -> error "addMissingPatterns: malformed function body"


-- | Make matches out of the given missing multipatterns.
mkMissingMatches :: Int -> String -> GallinaType -> [MultiPattern] -> [GallinaMatch]
mkMissingMatches arity name resultTy ms = zipWith (\mp n -> GallinaMatch (removeAnnotations mp) (term n)) ms ([0..] :: [Int])
  where
    term n  = GallinaLam eqArgs $ foldl1 GallinaApp $ [GallinaVar "False_rec", GallinaTermTy resultTy, foldl1 GallinaApp (GallinaVar (nonThm n) : map GallinaVar args)]
    eqArgs = map (\n -> "_h" ++ show n) [0 .. arity - 1]
    args = ('x' : show arity) : eqArgs
    nonThm n = name ++ "_acc_non_" ++ show n

-- | Add the inversion theorems as arguments to the recursive calls.
adjustExistingMatches :: GallinaFunctionBody -> [GallinaMatch]
adjustExistingMatches fun = zipWith (\m n -> m { matchTerm = GallinaLam (map (\o -> "_h" ++ show o) [0 .. arity - 1])
                                                             (manipulateTerm arity n name (matchTerm m)) })
                            ms
                            [0 ..]
  where
    ms = extractMatches fun
    name = funName fun
    arity = funArity fun

-- | Annotated multipattern.
type MultiPattern = [GallinaPatAnnotated]

-- | Find the missing multipatterns of a function definition.
missingPats :: TypeConstructors -> Specifications -> GallinaFunctionBody -> [MultiPattern]
missingPats tycons specs fun = evalState (algorithm tycons specs initialPatSubs (initialIdealMultiPat (funSpec fun))) 0
   where
     pats = map (annotatePats specs (funSpec fun) . matchPats) (extractMatches fun)
     initialPatSubs = zipWith (\p q -> (p, fromJust (unifyMultiPats q p)))
                      pats
                      (repeat (initialIdealMultiPat (funSpec fun)))

initialIdealMultiPat :: Specification -> MultiPattern
initialIdealMultiPat (Spec args _) = zipWith (\ty n -> GallinaPVarAnn ("_q" ++ show n) ty) args ([0..] :: [Int])

-- | Multipattern substitution. We also associate with a substitution
-- of a variable to pattern the type of the variable we substitute.
data MultiPatSubst =
  Compose MultiPatSubst MultiPatSubst
  | Subst String GallinaType GallinaPatAnnotated
  | IdSubst
    deriving Show

-- | Try to unify two multipatterns. We assume that @length ps0 ==
-- length ps1@, i.e. no malformed pats.
unifyMultiPats :: MultiPattern -> MultiPattern -> Maybe MultiPatSubst
unifyMultiPats l r = fmap (foldr Compose IdSubst)
                     $ sequence
                     $ zipWith unifyPatAnn l r

-- | Unify two annotated patterns. We assume that the patterns are
-- linear, i.e. every variable in the multipattern occurs exactly
-- once.
unifyPatAnn :: GallinaPatAnnotated -> GallinaPatAnnotated -> Maybe MultiPatSubst
unifyPatAnn (GallinaPVarAnn v t   ) p = Just $ Subst v t p
unifyPatAnn (GallinaPAppAnn c0 ps0) (GallinaPAppAnn c1 ps1)
  | c0 /= c1 = Nothing
  | otherwise = do
    substs <- sequence . map (uncurry unifyPatAnn) $ zip ps0 ps1
    return . foldr Compose IdSubst $ substs
unifyPatAnn (GallinaPTupleAnn ps0 ) (GallinaPTupleAnn ps1) = do
  substs <- sequence . map (uncurry unifyPatAnn) $ zip ps0 ps1
  return . foldr Compose IdSubst $ substs
unifyPatAnn _                       _                      = Nothing

-- | Apply a multipattern substitution.
applyMultiPatSubst :: MultiPatSubst -> MultiPattern -> MultiPattern
applyMultiPatSubst = map . applyPatSubst
  where
    applyPatSubst :: MultiPatSubst -> GallinaPatAnnotated -> GallinaPatAnnotated
    applyPatSubst IdSubst           = id
    applyPatSubst (Compose l r    ) = applyPatSubst l . applyPatSubst r
    applyPatSubst (Subst var _ pat) = applyVarSubst var pat
    applyVarSubst :: String -> GallinaPatAnnotated -> GallinaPatAnnotated -> GallinaPatAnnotated
    applyVarSubst v0 pat0 pat1@(GallinaPVarAnn v1 _  ) = if v0 == v1 then pat0 else pat1
    applyVarSubst v0 pat0 (GallinaPAppAnn constr pats) = GallinaPAppAnn constr
                                                         . map (applyVarSubst v0 pat0)
                                                         $ pats
    applyVarSubst v0 pat0 (GallinaPTupleAnn pats     ) = GallinaPTupleAnn
                                                         . map (applyVarSubst v0 pat0)
                                                         $ pats

-- | Find a non-renaming in a substitution: returns 'Nothing' if the
-- substitution only rename variables to variables (injectively, but
-- we do not check that) or return @'Just' x@ where @x@ is a variable
-- mapped to a non-variable.
hasNonRenaming :: MultiPatSubst -> Maybe (String, GallinaType)
hasNonRenaming IdSubst                          = Nothing
hasNonRenaming (Subst _ _ (GallinaPVarAnn _ _)) = Nothing
hasNonRenaming (Subst s t _                   ) = Just (s, t)
hasNonRenaming (Compose l r                   ) = hasNonRenaming l
                                                  `mplus` hasNonRenaming r

algorithm :: TypeConstructors -> Specifications -> [(MultiPattern, MultiPatSubst)] -> MultiPattern -> State Int [MultiPattern]
algorithm _      _     []            idealMultiPat = return [idealMultiPat]
algorithm tycons specs a@((_, s1):_) idealMultiPat = if not (invariantHolds a idealMultiPat) then error "oei!" else
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

-- | Fetch the left-most type constructor.
getTypeConstr :: GallinaType -> String
getTypeConstr (GallinaTyTuple s    ) = "* " ++ show (length s) -- urgh
getTypeConstr (GallinaTyList _     ) = "list"
getTypeConstr (GallinaTyApp l _    ) = getTypeConstr l
getTypeConstr (GallinaTyCon c      ) = c
getTypeConstr (GallinaTyTerm _     ) = error "getTypeConstr: terms should not occur here."
getTypeConstr (GallinaTyForall _ _ ) = error "getTypeConstr: foralls should not occur here."
getTypeConstr (GallinaTyFun _ _    ) = error "getTypeConstr: function types should not occur here."
getTypeConstr (GallinaTyVar _      ) = error "getTypeConstr: type var should not occur here."
getTypeConstr GallinaTySet           = error "getTypeConstr: set type should not occur here."
getTypeConstr GallinaTyProp          = error "getTypeConstr: prop type should not occur here."
getTypeConstr (GallinaTyPi _ _     ) = error "getTypeConstr: pi types should not occur here."
getTypeConstr (GallinaTyEq _ _     ) = error "getTypeConstr: type equalities should not occur here."

maybeTuple :: (a, Maybe b) -> Maybe (a, b)
maybeTuple (_, Nothing) = Nothing
maybeTuple (a, Just b ) = return (a, b)

-- splitVar should also get the type to find out how we have to split.
splitVar :: TypeConstructors -> Specifications -> GallinaType -> Int -> String -> MultiPattern -> [MultiPattern]
splitVar tycons specs ty n var ideal = map (\s -> applyMultiPatSubst s ideal) substs where
  substs = map (Subst var ty) pats
  pats = fromJust $ do
    constrNames <- M.lookup (getTypeConstr ty) tycons
    constrSpecs <- mapM (\v -> maybeTuple (v, M.lookup v specs)) constrNames
    let actualSpecs = map (second (flip substituteSpec ty)) constrSpecs
    return . map (uncurry mkPat) $ actualSpecs
  mkPat c (Spec args _) = GallinaPAppAnn c $ zipWith (\t m -> GallinaPVarAnn ("_p" ++ show n ++ "x" ++ show m) t) args ([0..] :: [Int])

-- Manipulate terms
manipulateTerm :: Int -> Int -> String -> GallinaTerm -> GallinaTerm
manipulateTerm arity m recFunName term = let (t',_,_) = count' 0 term True
                     in t'
  where
    invThm n = recFunName ++ "_acc_inv_" ++ show m ++ "_" ++ show n
    count' :: Int -> GallinaTerm -> Bool -> (GallinaTerm, Int, Bool)
    count' n t@(GallinaVar str) isRight
      | isRight && recFunName == str = ( GallinaApp (GallinaVar str) (term' n)
                                     , n + 1
                                     , True
                                     )
      | recFunName == str           = ( t
                                     , n + 1
                                     , True
                                     )
      | otherwise                  = (t,n,False)
    count' n (GallinaList ts)   isRight
      | isRight                    = let (n', t') = sequence' n ts
                                     in (GallinaList t', n', False)
      where
        sequence' nn []     = (nn, [])
        sequence' nn (x:xs) = let (t', nn', b) = count' nn x True
                              in (if b then nn'+1 else nn', t' : snd (sequence' nn' xs))
    count' n (GallinaApp l r)  isRight
      | isRight && b                = ( GallinaApp (GallinaApp l' r') (term' n)
                                     , n''
                                     , b
                                     )
      | otherwise                  = (GallinaApp l' r'
                                     , n''
                                     , b
                                     )

      where
        (l', n' ,b) = count' n l False
        (r', n'',_) = count' n' r True
    count' n t b = trace "manipulateTerm: cannot manipulate terms that contain something other than applications, variables or lists." $ (t, n, b)
    term' n = foldl1 GallinaApp (GallinaVar (invThm n) : map GallinaVar args)
    eqArgs = map (\n -> "_h" ++ show n) [0 .. arity - 1]
    args = ('x' : show arity) : eqArgs

-- | Extract the inversion theorems of the Bove-Capretta predicate
-- corresponding to the given function definition.
extractInvTheorems :: Specifications -> GallinaFunctionBody -> [VernacularCommand]
extractInvTheorems specs fun = concat $ zipWith calls matches ([0 ..] :: [Int])
  where
    ncalls match n = length (calls match n)
    callHyps match n = map (\m -> "Hcall" ++ show m) [0 .. ncalls match n - 1]
    ctxEqHyps ctx n = ". intros " ++ unwords (zipWith (\_ m -> "Heq" ++ show n ++ "_ctx_" ++ show m) ctx ([0..] :: [Int]))
                      ++ ". " ++ unwords (zipWith (\_ m -> "try (rewrite <- Heq" ++ show n ++ "_ctx_" ++ show m ++ "). ") ctx ([0..] :: [Int]))
    eqHyps multipat = zipWith (\p n -> ". intros Heq" ++ show n ++ "; injection Heq" ++ show n ++ ctxEqHyps p n)
                      (contexts multipat)
                      [0 .. arity - 1]
    arity = funArity fun
    matches = extractMatches fun
    params = map (\v -> (v, GallinaTySet)) . foldr L.union [] . map freevars $ argTys
    context = concat . contexts
    contexts multipat = extractContexts specs (funSpec fun) multipat
    predArg = foldl GallinaTyApp (GallinaTyCon (predicateName fun)) $ map GallinaTyVar (map fst args)
    argTys = case funSpec fun of Spec a _ -> a
    args = zipWith (\n t -> ("x" ++ show n, t)) [0 .. arity - 1] argTys
    ty call multipat = foldr GallinaTyFun call
                       $ predArg : zipWith (\p n -> GallinaTyEq (GallinaTyVar ('x':show n)) (patternToType p)) multipat [0 .. arity - 1]

    calls match n = zipWith (mkTheorem match n) (collectRecursiveCalls fun match) ([0 ..] :: [Int])
    mkTheorem match n call m = GallinaThmDef $ GallinaTheorem
                           { theoremName = funName fun ++ "_acc_inv_" ++ show n ++ "_" ++ show m
                           , theoremProp = GallinaTyPi (params ++ args ++ context (matchPats match)) (ty call (matchPats match))
                           , theoremProof = "intros " ++ unwords (map fst (params ++ args ++ context (matchPats match)))
                                            ++ " H; case H; try (intros; discriminate)."
                                            ++ " intros " ++ unwords (map ((++ "'") . fst) (context (matchPats match)) ++ callHyps match n ++ eqHyps (matchPats match))
                                            ++ "assumption."
                           }
