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


data GallinaInductiveBody =
  GallinaInductiveBody { inductiveName    :: String
                       , inductiveParams  :: [String]
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
  deriving Show


data GallinaTerm =
  GallinaVar String
  | GallinaApp GallinaTerm GallinaTerm
  | GallinaLam [String] GallinaTerm
  | GallinaCase [GallinaTerm] [GallinaMatch]
  deriving Show

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
