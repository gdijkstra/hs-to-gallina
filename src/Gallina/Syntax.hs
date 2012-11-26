-- | Abstract syntax of a subset of the Coq Vernacular language and a
-- subset of the Gallina specification language.
module Gallina.Syntax where

import           Data.List  (union)
import           Data.Maybe (fromMaybe)

-- | Coq document: its name and the commands.
data VernacularDocument =
  VernacularDocument
  { documentName     :: String
  , documentCommands :: [VernacularCommand]
  }
  deriving (Show, Eq)

-- | Function or pattern binding body.
type FunOrPatBody = Either GallinaFunctionBody GallinaPatBindingBody

-- | Small subset of Vernacular commands.
data VernacularCommand =
  -- | Type synonym definition.
  GallinaTypeSynonym GallinaTypeSynBody
  -- | Inductive data type definition. 'Bool' indicates whether it is
  -- coinductive ('True') or not ('False').
  | GallinaInductive [GallinaInductiveBody] Bool
  -- | Function definition (non-recursive).
  | GallinaFunction GallinaFunctionBody
  -- | Pattern binding definition (i.e. function with no arguments).
  | GallinaPatBinding GallinaPatBindingBody
  -- | (Co)recursive definitions, possibly multiple mutually recursive
  -- functions/pattern bindings.
  | GallinaFixpoint [FunOrPatBody] Bool
  -- | Theorem definition.
  | GallinaThmDef GallinaTheorem
  -- | Turn on the implicit arguments...
  | GallinaSetImplicit
  -- | ...and turn them off.
  | GallinaUnsetImplicit
  deriving (Show, Eq)

-- | Type synonym definition.
data GallinaTypeSynBody =
  GallinaTypeSynBody
  {
    -- | Type synonym name.
    synonymName   :: String
    -- | The type parameters of the type synonym.
  , synonymParams :: [String]
    -- | The right-hand side of the type synonym definition.
  , synonymType   :: GallinaType
  }
  deriving (Show, Eq)

-- | Let definitions.
data GallinaLetDefinition =
  -- | Non-recursive local function definition.
  GallinaLetFunction GallinaFunctionBody
  -- | Non-recursive local pattern binding definition.
  | GallinaLetPatBinding GallinaPatBindingBody
  -- | Recursive local function / pattern binding definition.
  | GallinaLetFixpoint FunOrPatBody
  deriving (Show, Eq)

-- | Inductive data type definition.
data GallinaInductiveBody =
  GallinaInductiveBody
  {
    -- | Data type name.
    inductiveName    :: String
    -- | The type parameters of the data type.
  , inductiveParams  :: [String]
    -- | The type of the data type, e.g. 'GallinaTySet' for Haskell
    -- data types.
  , inductiveType    :: GallinaType
    -- | The constructors of the data type.
  , inductiveConstrs :: [GallinaConstructor]
  }
  deriving (Show, Eq)

-- | Constructor definition.
data GallinaConstructor =
  GallinaConstructor
  {
    -- | Name of the constructor.
    constrName :: String
    -- | Type of the constructor. Result type should be the type of
    -- the data type it belongs to.
  , constrType :: GallinaType
  }
  deriving (Show, Eq)

-- | Function definition.
data GallinaFunctionBody =
  GallinaFunctionBody
  {
    -- | Arity of the function.
    funArity :: Int
    -- | Name of the function.
  , funName  :: String
    -- | Type of the function. Can be 'Nothing' in the case of local
    -- definitions.
  , funType  :: Maybe GallinaType
    -- | Body of the function. Is generally expected to be a
    -- 'GallinaCase' term.
  , funBody  :: GallinaTerm
  }
  deriving (Show, Eq)

-- | Pattern binding definition.
data GallinaPatBindingBody =
  GallinaPatBindingBody
  {
    -- | Name of the pattern binding.
    patName :: String
    -- | Type of the pattern binding. Can be 'Nothing' in the case of
    -- local definitions.
  , patType :: Maybe GallinaType
    -- | Body of the pattern.
  , patBody :: GallinaTerm
  }
  deriving (Show, Eq)

-- | A pattern match equation.
data GallinaMatch =
  GallinaMatch
  {
    -- | The patterns...
    matchPats :: [GallinaPat]
    -- | ...and the corresponding expression.
  , matchTerm :: GallinaTerm
  }
  deriving (Show, Eq)

-- | Patterns.
data GallinaPat =
  -- | Pattern variable.
  GallinaPVar String
  -- | Application of a constructor to a list of patterns.
  | GallinaPApp String [GallinaPat]
  -- | Wildcard pattern.
  | GallinaPWildCard
  deriving (Show, Eq)

-- | Types.
data GallinaType =
  -- | Forall quantifiers. Binds the identifiers given in the list of
  -- 'String's.
  GallinaTyForall [String] GallinaType
  -- | Function arrow.
  | GallinaTyFun GallinaType GallinaType
  -- | Type application.
  | GallinaTyApp GallinaType GallinaType
  -- | Type variable.
  | GallinaTyVar String
  -- | Type constructor.
  | GallinaTyCon String
  -- | List type.
  | GallinaTyList GallinaType
  -- | Set type.
  | GallinaTySet
  -- | Prop type.
  | GallinaTyProp
  -- | Pi type. Same as 'GallinaTyForall', but the identifiers now can
  -- have other types than just 'GallinaTySet'.
  | GallinaTyPi [(String, GallinaType)] GallinaType
  -- | Equality type.
  | GallinaTyEq GallinaType GallinaType
  -- | A term as a type as needed for the Bove-Capretta method..
  | GallinaTyTerm GallinaTerm
  deriving (Show, Eq)

-- | Terms.
data GallinaTerm =
  -- | Variable.
  GallinaVar String
  -- | Application.
  | GallinaApp GallinaTerm GallinaTerm
  -- | Lambda abstraction. Binds the identifiers in the given term.
  | GallinaLam [String] GallinaTerm
  -- | Case expression. Matches on the given terms.
  | GallinaCase [GallinaTerm] [GallinaMatch]
  -- | Dependent pattern matching as needed for the Bove-Capretta method.
  -- @\"match \<term0\> as \<ident0\> , ... , \<termn\> as \<identn\> return \<type\> with \<matches\>\"@
  | GallinaDepCase [(GallinaTerm, String)] GallinaType [GallinaMatch]
  -- | Let definitions.
  | GallinaLet [GallinaLetDefinition] GallinaTerm
  -- | if-then-else expression.
  | GallinaIf GallinaTerm GallinaTerm GallinaTerm
  -- | Type as a term as needed for the Bove-Capretta method.
  | GallinaTermTy GallinaType
  -- | List expression.
  | GallinaList [GallinaTerm]
  deriving (Show, Eq)

-- | Theorem definition.
data GallinaTheorem =
  GallinaTheorem
  {
    -- | Name of the theorem.
    theoremName  :: String
    -- | Theorem statement.
  , theoremProp  :: GallinaType
    -- | Proof of the statement.
  , theoremProof :: String
  }
  deriving (Show, Eq)

-- | Bind all the free type variables using 'GallinaTyForall'.
generalise :: GallinaType -> GallinaType
generalise ty = let vars = ftv ty in if not (null vars)
                                     then GallinaTyForall vars ty
                                     else ty

-- | Take the union of the lists.
unions :: Eq a => [[a]] -> [a]
unions = foldr union []

-- | Calculate the free type variables.
ftv :: GallinaType -> [String]
ftv (GallinaTyForall _ _ ) = error "ftv: foralls should not occur here."
ftv (GallinaTyPi _ _     ) = error "ftv: pi types should not occur here."
ftv (GallinaTyTerm _     ) = error "ftv: terms should not occur here."
ftv (GallinaTyEq l r     ) = union (ftv l) (ftv r)
ftv (GallinaTyFun l r    ) = union (ftv l) (ftv r)
ftv (GallinaTyApp l r    ) = union (ftv l) (ftv r)
ftv (GallinaTyVar str    ) = return str
ftv (GallinaTyCon _      ) = []
ftv (GallinaTySet        ) = []
ftv (GallinaTyProp       ) = []
ftv (GallinaTyList t     ) = ftv t

-- | Flatten a type, i.e. replace the GallinaTyFun constructor by (:).
flatTy :: GallinaType -> [GallinaType]
flatTy (GallinaTyForall _ ty   ) = flatTy ty
flatTy (GallinaTyFun l r       ) = l : flatTy r
flatTy ty@(GallinaTyApp _ _    ) = [ty]
flatTy ty@(GallinaTyVar _      ) = [ty]
flatTy ty@(GallinaTyCon _      ) = [ty]
flatTy ty@(GallinaTySet        ) = [ty]
flatTy ty@(GallinaTyProp       ) = [ty]
flatTy ty@(GallinaTyList _     ) = [ty]
flatTy (GallinaTyTerm _        ) = error "flatTy: terms should not occur here."
flatTy (GallinaTyPi _ _        ) = error "flatTy: pi types should not occur here."
flatTy (GallinaTyEq _ _        ) = error "flatTy: equality types should not occur here."

-- | Unflatten a type, i.e. inverse of flatTy. Returns 'Nothing' if
-- the list is empty.
unflatTy :: [GallinaType] -> Maybe GallinaType
unflatTy []     = Nothing
unflatTy [x]    = Just x
unflatTy (x:xs) = do
  uxs <- unflatTy xs
  return $ GallinaTyFun x uxs

-- | Given the arity of a (function) type, split the type into a list
-- of the types of the arguments and the type of the result. Will
-- yield an error if the arity does not match the type.
argsResTy :: Int -> GallinaType -> ([GallinaType], GallinaType)
argsResTy arity (GallinaTyForall _ ty) = argsResTy arity ty
argsResTy arity ty@(GallinaTyFun _ _ ) = ( take arity . flatTy $ ty
                                         , fromMaybe errorMsg . unflatTy
                                           . drop arity . flatTy $ ty
                                         )
  where
    errorMsg = error "argsResTy: unflattening failed: arity too high"
argsResTy _     _                      = error "argsResTy: not a function type"

-- | Fetch the result type of a function type. Might crash for the
-- same reasons 'argsResTy' may crash.
resTy :: Int -> GallinaType -> GallinaType
resTy arity ty = snd . argsResTy arity $ ty

-- | Find all the variables in a pattern.
patVars :: GallinaPat -> [String]
patVars (GallinaPVar s    ) = [s]
patVars (GallinaPApp s ps ) = s : concatMap patVars ps
patVars GallinaPWildCard    = []
