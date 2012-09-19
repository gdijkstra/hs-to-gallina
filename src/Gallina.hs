module Gallina where

import Data.List

data GallinaDataType = GallinaDataType { dataTypeName :: String
                                       , constrs :: [GallinaConstructor] }

data GallinaConstructor = GallinaConstructor { constrName :: String
                                             , fields :: [String]
                                             }
  
ppDataType :: GallinaDataType -> String
ppDataType d = "Inductive " ++ dataTypeName d ++ " : Set :="
               ++ (concatMap  ("\n  | "++) . map (ppConstr (dataTypeName d)) . constrs $ d)

               
ppConstr :: String -> GallinaConstructor -> String
ppConstr n c  = constrName c ++ " : " ++ ( intercalate " -> " . (++ [n]) . fields $ c)

booleans :: GallinaDataType
booleans = GallinaDataType "Bool" [GallinaConstructor "True" [], GallinaConstructor "False" []]
