module Gallina.Syntax where

import           Data.List

data Vernacular =
  Vernacular
  { moduleName        :: String
  , moduleDefinitions :: [GallinaDefinition]
  }
  deriving Show

type FunOrPatBody = Either GallinaFunctionBody GallinaPatBindingBody

data GallinaUngroupedDefinition =
  GallinaUngroupedInd GallinaInductiveBody
  | GallinaUngroupedFunOrPat FunOrPatBody
  deriving Show

data GallinaDefinition =
  GallinaInductive [GallinaInductiveBody]
  | GallinaFunction GallinaFunctionBody
  | GallinaPatBinding GallinaPatBindingBody
  | GallinaFixpoint [Either GallinaFunctionBody GallinaPatBindingBody]
  deriving Show

data GallinaLetDefinition =
  GallinaLetFunction GallinaFunctionBody
  | GallinaLetPatBinding GallinaPatBindingBody
  | GallinaLetFixpoint (Either GallinaFunctionBody GallinaPatBindingBody)
  deriving Show

data GallinaInductiveBody =
  GallinaInductiveBody { inductiveName    :: String
                       , inductiveParams  :: [String]
                       , inductiveType    :: GallinaType
                       , inductiveConstrs :: [GallinaConstructor] }
  deriving Show


data GallinaConstructor =
  GallinaConstructor
  { constrName :: String
  , constrType :: GallinaType
  }
  deriving Show


data GallinaFunctionBody =
  GallinaFunctionBody
  { funArity :: Int
  , funName  :: String
  , funType  :: Maybe GallinaType
  , funBody  :: GallinaTerm
  }
  deriving Show


data GallinaPatBindingBody =
  GallinaPatBindingBody
  { patName :: String
  , patType :: Maybe GallinaType
  , patBody :: GallinaTerm
  }
  deriving Show


data GallinaMatch =
  GallinaMatch
  { matchPats :: [GallinaPat]
  , matchTerm :: GallinaTerm
  }
  deriving Show


data GallinaPat =
  GallinaPVar String
  | GallinaPApp String [GallinaPat]
  | GallinaPWildCard
  deriving Show


data GallinaType =
  GallinaTyForall [String] GallinaType
  | GallinaTyFun GallinaType GallinaType
  | GallinaTyApp GallinaType GallinaType
  | GallinaTyVar String
  | GallinaTyCon String
  | GallinaTySet
  deriving Show


data GallinaTerm =
  GallinaVar String
  | GallinaApp GallinaTerm GallinaTerm
  | GallinaLam [String] GallinaTerm
  | GallinaCase [GallinaTerm] [GallinaMatch]
  | GallinaLet [GallinaLetDefinition] GallinaTerm
  | GallinaIf GallinaTerm GallinaTerm GallinaTerm
  deriving Show

-- Utility functions on types.
generalise :: GallinaType -> GallinaType
generalise ty = let vars = ftv ty in if not (null vars)
                                     then GallinaTyForall vars ty
                                     else ty

ftv :: GallinaType -> [String]
ftv (GallinaTyForall _ _ ) = error "ftv: foralls should not occur here"
ftv (GallinaTyFun l r    ) = union (ftv l) (ftv r)
ftv (GallinaTyApp l r    ) = union (ftv l) (ftv r)
ftv (GallinaTyVar str    ) = return str
ftv (GallinaTyCon _      ) = []
ftv (GallinaTySet        ) = []

-- Replace the GallinaTy constructor by (:).
flatTy :: GallinaType -> [GallinaType]
flatTy (GallinaTyForall _ ty ) = flatTy ty
flatTy (GallinaTyFun l r     ) = l : flatTy r
flatTy ty@(GallinaTyApp _ _  ) = [ty]
flatTy ty@(GallinaTyVar _    ) = [ty]
flatTy ty@(GallinaTyCon _    ) = [ty]
flatTy ty@(GallinaTySet      ) = [ty]

-- Inverse of flatTy.
unflatTy :: [GallinaType] -> Maybe GallinaType
unflatTy []     = Nothing
unflatTy [x]    = Just x
unflatTy (x:xs) = do
  uxs <- unflatTy xs
  return $ GallinaTyFun x uxs

-- Utility function on patterns.
patVars :: GallinaPat -> [String]
patVars (GallinaPVar s    ) = [s]
patVars (GallinaPApp s ps ) = s : concatMap patVars ps
patVars GallinaPWildCard    = []

