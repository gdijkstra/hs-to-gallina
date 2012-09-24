module Gallina where

import Data.List

-- http://coq.inria.fr/refman/Reference-Manual003.html

data Vernacular = Vernacular { moduleName :: String 
                             , dataTypes :: [GallinaDataType]
                             , definitions :: [GallinaDefinition]
                             }

data GallinaDecl = GallinaDataTypeDecl GallinaDataType
                 | GallinaFunctionBinding String GallinaType GallinaTerm
                 | GallinaTypeSigDecl String GallinaType

data GallinaDataType = GallinaDataType { dataTypeName :: String
                                       , constrs :: [GallinaConstructor] }

data GallinaConstructor = GallinaConstructor { constrName :: String
                                             , fields :: [String]
                                             }

data GallinaType
     = GallinaTyForall [String] GallinaType
     | GallinaTyFun GallinaType GallinaType        
     | GallinaTyVar String
     | GallinaTyCon String

data GallinaDefinition = GallinaDefinition { defName :: String
                                           , defType :: GallinaType
                                           , defBody :: GallinaTerm
                                           }

data GallinaTerm = GallinaLam [String] GallinaTerm
                 | GallinaApp GallinaTerm GallinaTerm
                 | GallinaVar String
-- and pattern matching etc.

ppVernacular :: Vernacular -> String
ppVernacular v = "Module " ++ moduleName v ++ ".\n\n" 
                 ++ (intercalate "\n\n" . map ppDataType . dataTypes $ v) ++ "\n"
                 ++ (intercalate "\n\n" . map ppDefinition . definitions $ v)
                 ++ "\n# data types: " ++ show l
  where l = length . dataTypes $ v
  
ppDataType :: GallinaDataType -> String
ppDataType d = "Inductive " ++ dataTypeName d ++ " : Set :="
               ++ (concatMap  ("\n  | "++) . map (ppConstr (dataTypeName d)) . constrs $ d)
               ++ "."

               
ppConstr :: String -> GallinaConstructor -> String
ppConstr n c  = constrName c ++ " : " ++ ( intercalate " -> " . (++ [n]) . fields $ c)

ppDefinition :: GallinaDefinition -> String
ppDefinition d = "Definition " ++ defName d 
                 ++ " " ++ (ppBoundVars . defType $ d)
                 ++ " : " ++ (ppType . defType $ d) ++ " :=\n\t" ++ (ppTerm . defBody $ d) ++ "."

        
testDefinition :: GallinaDefinition
testDefinition = GallinaDefinition "const" (GallinaTyForall ["a", "b"] (GallinaTyFun (GallinaTyVar "a") (GallinaTyFun (GallinaTyVar "b") (GallinaTyVar "a")))) undefined

ppBoundVars :: GallinaType -> String
ppBoundVars (GallinaTyForall l _) = if not (null l)
                                    then "{ " ++ unwords l ++ " : Type }"
                                    else ""
ppBoundVars _ = ""

-- Ignore foralls
ppType :: GallinaType -> String
ppType (GallinaTyForall _ t) = ppType t
ppType (GallinaTyFun l r) = ppType l ++ " -> " ++ ppType r -- TODO: parentheses
ppType (GallinaTyVar str) = str
ppType (GallinaTyCon str) = str

ppTerm :: GallinaTerm -> String
ppTerm _ = ""

generalise :: GallinaType -> GallinaType
generalise ty = let vars = ftv ty in if not (null vars) 
                                     then GallinaTyForall vars ty
                                     else ty

ftv :: GallinaType -> [String]
ftv (GallinaTyForall _ _) = error "ftv: foralls should not occur here"
ftv (GallinaTyFun l r) = union (ftv l) (ftv r)
ftv (GallinaTyVar str) = return str
ftv (GallinaTyCon str) = return str
