module Gallina.Syntax where

import           Data.List

data Vernacular =
  Vernacular
  { moduleName        :: String
  , moduleDefinitions :: [GallinaDefinition]
  }

data GallinaUngroupedDefinition =
  GallinaUngroupedInd GallinaInductiveBody
  | GallinaUngroupedFunOrPat (Either GallinaFunctionBody GallinaPatBindingBody)

data GallinaDefinition =
  GallinaInductive [GallinaInductiveBody]
  | GallinaFunction GallinaFunctionBody
  | GallinaPatBinding GallinaPatBindingBody
  | GallinaFixpoint [Either GallinaFunctionBody GallinaPatBindingBody]

data GallinaInductiveBody =
  GallinaInductiveBody { inductiveName    :: String
                       , inductiveParams  :: [String]
                       , inductiveConstrs :: [GallinaConstructor] }

data GallinaConstructor =
  GallinaConstructor
  { constrName :: String
  , constrType :: GallinaType
  }

data GallinaFunctionBody =
  GallinaFunctionBody
  { funArity :: Int
  , funName  :: String
  , funType  :: GallinaType
  , funBody  :: GallinaTerm
  }

data GallinaPatBindingBody =
  GallinaPatBindingBody
  { patName :: String
  , patType :: GallinaType
  , patBody :: GallinaTerm
  }

data GallinaMatch =
  GallinaMatch
  { matchPats :: [GallinaPat]
  , matchTerm :: GallinaTerm
  }

data GallinaPat =
  GallinaPVar String
  | GallinaPApp String [GallinaPat]
  | GallinaPWildCard

data GallinaType =
  GallinaTyForall [String] GallinaType
  | GallinaTyFun GallinaType GallinaType
  | GallinaTyApp GallinaType GallinaType
  | GallinaTyVar String
  | GallinaTyCon String

data GallinaTerm =
  GallinaVar String
  | GallinaApp GallinaTerm GallinaTerm
  | GallinaLam [String] GallinaTerm
  | GallinaCase [GallinaTerm] [GallinaMatch]

generalise :: GallinaType -> GallinaType
generalise ty = let vars = ftv ty in if not (null vars)
                                     then GallinaTyForall vars ty
                                     else ty

ftv :: GallinaType -> [String]
ftv (GallinaTyForall _ _) = error "ftv: foralls should not occur here"
ftv (GallinaTyFun l r) = union (ftv l) (ftv r)
ftv (GallinaTyApp l r) = union (ftv l) (ftv r)
ftv (GallinaTyVar str) = return str
ftv (GallinaTyCon _) = []

patVars :: GallinaPat -> [String]
patVars (GallinaPVar s) = [s]
patVars (GallinaPApp s ps) = s : concatMap patVars ps
patVars GallinaPWildCard = []
