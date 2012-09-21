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

data GallinaType = GallinaType { tyBoundVars :: [String] 
                               , tyArgs :: [String] 
                               , tyResult :: String
                               }

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
                 ++ (if (not . null . tyBoundVars . defType $ d) 
                    then " { " ++ (unwords . tyBoundVars . defType $ d) ++ " : Type }"
                    else "")
                 ++ " : " ++ intercalate " -> " t ++ " :=\n\t" ++ (ppTerm . defBody $ d) ++ "."
  where t = tyArgs (defType d) ++ [tyResult (defType d)]
        
testDefinition = GallinaDefinition "const" (GallinaType ["a", "b"] ["a", "b"] "a") undefined

ppTerm :: GallinaTerm -> String
ppTerm t = ""
