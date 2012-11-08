module Gallina.Syntax where

import           Data.List
import           Data.Maybe

data Vernacular =
  Vernacular
  { moduleName        :: String
  , moduleDefinitions :: [GallinaDefinition]
  }
  deriving (Show, Eq)

type FunOrPatBody = Either GallinaFunctionBody GallinaPatBindingBody

data GallinaUngroupedDefinition =
  GallinaUngroupedInd GallinaInductiveBody
  | GallinaUngroupedFunOrPat FunOrPatBody
  deriving (Show, Eq)

data GallinaDefinition =
  GallinaInductive [GallinaInductiveBody]
  | GallinaFunction GallinaFunctionBody
  | GallinaPatBinding GallinaPatBindingBody
  | GallinaFixpoint [Either GallinaFunctionBody GallinaPatBindingBody]
  | GallinaThmDef GallinaTheorem
  | GallinaSetImplicit
  | GallinaUnsetImplicit
  deriving (Show, Eq)

data GallinaLetDefinition =
  GallinaLetFunction GallinaFunctionBody
  | GallinaLetPatBinding GallinaPatBindingBody
  | GallinaLetFixpoint (Either GallinaFunctionBody GallinaPatBindingBody)
  deriving (Show, Eq)

data GallinaInductiveBody =
  GallinaInductiveBody
  { inductiveName    :: String
  , inductiveParams  :: [String]
  , inductiveType    :: GallinaType
  , inductiveConstrs :: [GallinaConstructor]
  }
  deriving (Show, Eq)


data GallinaConstructor =
  GallinaConstructor
  { constrName :: String
  , constrType :: GallinaType
  }
  deriving (Show, Eq)


data GallinaFunctionBody =
  GallinaFunctionBody
  { funArity :: Int
  , funName  :: String
  , funType  :: Maybe GallinaType
  , funBody  :: GallinaTerm
  }
  deriving (Show, Eq)


data GallinaPatBindingBody =
  GallinaPatBindingBody
  { patName :: String
  , patType :: Maybe GallinaType
  , patBody :: GallinaTerm
  }
  deriving (Show, Eq)


data GallinaMatch =
  GallinaMatch
  { matchPats :: [GallinaPat]
  , matchTerm :: GallinaTerm
  }
  deriving (Show, Eq)


data GallinaPat =
  GallinaPVar String
  | GallinaPApp String [GallinaPat]
  | GallinaPWildCard
  deriving (Show, Eq)


data GallinaType =
  GallinaTyForall [String] GallinaType
  | GallinaTyFun GallinaType GallinaType
  | GallinaTyApp GallinaType GallinaType
  | GallinaTyVar String
  | GallinaTyCon String
  | GallinaTySet
  | GallinaTyPi [(String, GallinaType)] GallinaType
  | GallinaTyEq GallinaType GallinaType
  deriving (Show, Eq)


data GallinaTerm =
  GallinaVar String
  | GallinaApp GallinaTerm GallinaTerm
  | GallinaLam [String] GallinaTerm
  | GallinaCase [GallinaTerm] [GallinaMatch]
  | GallinaDepCase [(GallinaTerm, String)] GallinaType [GallinaMatch]
  | GallinaLet [GallinaLetDefinition] GallinaTerm
  | GallinaIf GallinaTerm GallinaTerm GallinaTerm
  | GallinaTyTerm GallinaType
  deriving (Show, Eq)

data GallinaTheorem =
  GallinaTheorem
  { theoremName  :: String
  , theoremProp  :: GallinaType
  , theoremProof :: String
  }
  deriving (Show, Eq)

-- Utility functions on types.
generalise :: GallinaType -> GallinaType
generalise ty = let vars = ftv ty in if not (null vars)
                                     then GallinaTyForall vars ty
                                     else ty

ftv :: GallinaType -> [String]
ftv (GallinaTyForall _ _ ) = error "ftv: foralls should not occur here"
ftv (GallinaTyPi _ _     ) = error "ftv: pi types should not occur here"
ftv (GallinaTyEq l r     ) = union (ftv l) (ftv r)
ftv (GallinaTyFun l r    ) = union (ftv l) (ftv r)
ftv (GallinaTyApp l r    ) = union (ftv l) (ftv r)
ftv (GallinaTyVar str    ) = return str
ftv (GallinaTyCon _      ) = []
ftv (GallinaTySet        ) = []

-- Replace the GallinaTyFun constructor by (:).
flatTy :: GallinaType -> [GallinaType]
flatTy (GallinaTyForall _ ty ) = flatTy ty
flatTy (GallinaTyFun l r     ) = l : flatTy r
flatTy ty@(GallinaTyApp _ _  ) = [ty]
flatTy ty@(GallinaTyVar _    ) = [ty]
flatTy ty@(GallinaTyCon _    ) = [ty]
flatTy ty@(GallinaTySet      ) = [ty]
flatTy (GallinaTyPi _ _      ) = error "flatTy: pi types should not occur here"
flatTy (GallinaTyEq _ _      ) = error "flatTy: equality types should not occur here"

-- Inverse of flatTy.
unflatTy :: [GallinaType] -> Maybe GallinaType
unflatTy []     = Nothing
unflatTy [x]    = Just x
unflatTy (x:xs) = do
  uxs <- unflatTy xs
  return $ GallinaTyFun x uxs

argsResTy :: Int -> GallinaType -> ([GallinaType], GallinaType)
argsResTy arity (GallinaTyForall _ ty) = argsResTy arity ty
argsResTy arity ty@(GallinaTyFun _ _ ) = ( take arity . flatTy $ ty
                                         , fromMaybe errorMsg . unflatTy
                                           . drop arity . flatTy $ ty
                                         )
  where
    errorMsg = error "argsResTy: unflattening failed: arity too high"
argsResTy _     _                      = error "argsResTy: not a function type"

resTy :: Int -> GallinaType -> GallinaType
resTy arity ty = snd . argsResTy arity $ ty

-- Utility function on patterns.
patVars :: GallinaPat -> [String]
patVars (GallinaPVar s    ) = [s]
patVars (GallinaPApp s ps ) = s : concatMap patVars ps
patVars GallinaPWildCard    = []

