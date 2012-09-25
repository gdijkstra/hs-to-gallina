module Gallina where

import Data.List
import Text.PrettyPrint.HughesPJ

class Pp a where
  pp :: a -> Doc

data Vernacular = Vernacular { moduleName :: String 
                             , moduleDataTypes :: [GallinaInductive]
                             , moduleDefinitions :: [GallinaDefinition]
                             }

data GallinaInductive = GallinaInductive { inductiveName :: String
                                         , inductiveConstrs :: [GallinaConstructor] }


data GallinaConstructor = GallinaConstructor { constrName :: String
                                             , constrType :: GallinaType
                                             }

data GallinaDefinition = GallinaDefinition { defName :: String
                                           , defType :: GallinaType
                                           , defBody :: GallinaFunBody
                                           }

data GallinaFunBody = GallinaFunBody { funArity :: Int
                                     , funMatches :: [GallinaMatch]
                                     }

data GallinaMatch = GallinaMatch { matchPats :: [GallinaPat] 
                                 , matchTerm :: GallinaTerm
                                 }

data GallinaPat = GallinaPVar String
                | GallinaPApp String [GallinaPat]
                | GallinaPWildCard

data GallinaType
     = GallinaTyForall [String] GallinaType
     | GallinaTyFun GallinaType GallinaType        
     | GallinaTyVar String
     | GallinaTyCon String


data GallinaTerm = GallinaVar String

-- Pretty printing

commas :: [Doc] -> Doc
commas = hsep . intersperse (text ",") -- TODO: fix unnecessary spaces

vsep :: [Doc] -> Doc
vsep = vcat . intersperse (text "")

ppVernacular :: Vernacular -> String
ppVernacular = render . pp

instance Pp Vernacular where
  pp a = vsep [text "Module " <+> text (moduleName a) <> text "."
              , vsep (map pp (moduleDataTypes a))
              , vsep (map pp (moduleDefinitions a))
              ]

instance Pp GallinaInductive where
  pp a = text "Inductive" <+> text (inductiveName a) <+> text ": Set :="
          $+$ nest 2 (vcat (map (\x -> text "|" <+> pp x) (inductiveConstrs a))
                      <> text ".")
  
instance Pp GallinaConstructor where
  pp a = text (constrName a) <+> text ":" <+> pp (constrType a)

instance Pp GallinaDefinition where
  pp a = text "Definition" <+> text (defName a) 
         <+> ppDefType (defType a) <+> text ":="
         $$ nest 2 (pp (defBody a) <> text ".")
    where ppDefType (GallinaTyForall vars ty) = (if not (null vars)
                                                     then text "{" <+> hsep (map text vars)
                                                          <+> text ": Type" <+> text "}" 
                                                     else empty) <+> text ":" <+> pp ty
          ppDefType ty = text ":" <+> pp ty

instance Pp GallinaFunBody where
  pp a = text "fun" 
          <+> hsep args
          <+> text "=>" 
          $$ nest 2 (text "match" <+> commas args <+> text "with" 
                      $+$ nest 2 (vcat (map pp (funMatches a)))
                      $+$ text "end")
    where args = (map (\n -> text "x" <> text (show n)) [0 .. (funArity a - 1)])

instance Pp GallinaMatch where
  pp a = text "|" <+> commas (map pp (matchPats a)) 
             <+> text "=>" <+> pp (matchTerm a)

instance Pp GallinaPat where
  pp (GallinaPVar s) = text s
  pp (GallinaPApp s ps) = hsep (text s : map pp ps)
  pp GallinaPWildCard = text "_"

instance Pp GallinaType where
  pp (GallinaTyForall _ ty) = pp ty -- TODO: do smth with vars
  pp (GallinaTyFun l r) = pp l <+> text "->" <+> pp r -- TODO: parentheses
  pp (GallinaTyVar s) = text s
  pp (GallinaTyCon s) = text s
  
instance Pp GallinaTerm where  
  pp (GallinaVar s) = text s

generalise :: GallinaType -> GallinaType
generalise ty = let vars = ftv ty in if not (null vars) 
                                     then GallinaTyForall vars ty
                                     else ty

ftv :: GallinaType -> [String]
ftv (GallinaTyForall _ _) = error "ftv: foralls should not occur here"
ftv (GallinaTyFun l r) = union (ftv l) (ftv r)
ftv (GallinaTyVar str) = return str
ftv (GallinaTyCon _) = []

-- TODO: remove this, someday.
testDefinition :: GallinaDefinition
testDefinition = GallinaDefinition "const" (GallinaTyForall ["a", "b"] (GallinaTyFun (GallinaTyVar "a") (GallinaTyFun (GallinaTyVar "b") (GallinaTyVar "a")))) body
  where body = GallinaFunBody 2 [GallinaMatch [GallinaPVar "a", GallinaPVar "b"] (GallinaVar "a")]

