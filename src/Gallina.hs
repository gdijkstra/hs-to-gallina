module Gallina where

import Data.List
import Text.PrettyPrint.HughesPJ

data Vernacular = Vernacular { moduleName :: String 
                             , moduleDataTypes :: [GallinaInductive]
                             , moduleDefinitions :: [GallinaDefinition]
                             }

data GallinaInductive = GallinaInductive { inductiveName :: String
                                         , inductiveParams :: [String]
                                         , inductiveConstrs :: [GallinaConstructor] }


data GallinaConstructor = GallinaConstructor { constrName :: String
                                             , constrType :: GallinaType
                                             }

data GallinaDefinition = GallinaDefinition { defName :: String
                                           , defType :: GallinaType
                                           , defBody :: GallinaBody
                                           }

data GallinaBody = GallinaFunBody { funArity :: Int
                                  , funMatches :: [GallinaMatch]
                                  }
                 | GallinaPatBody GallinaTerm


data GallinaMatch = GallinaMatch { matchPats :: [GallinaPat] 
                                 , matchTerm :: GallinaTerm
                                 }

data GallinaPat = GallinaPVar String
                | GallinaPApp String [GallinaPat]
                | GallinaPWildCard

data GallinaType
     = GallinaTyForall [String] GallinaType
     | GallinaTyFun GallinaType GallinaType        
     | GallinaTyApp GallinaType GallinaType        
     | GallinaTyVar String
     | GallinaTyCon String

data GallinaTerm = GallinaVar String
                 | GallinaApp GallinaTerm GallinaTerm
                 | GallinaLam [String] GallinaTerm
                 | GallinaCase GallinaTerm [GallinaMatch]

-- Pretty printing

class Pp a where
  pp :: a -> Doc
  ppPrec :: Int -> a -> Doc
  
  pp = ppPrec 0
  ppPrec _ = pp

parensIf :: Bool -> Doc -> Doc
parensIf b = if b then parens else id

commas :: [Doc] -> Doc
commas = hsep . intersperse (text ",") -- TODO: fix unnecessary spaces

vsep :: [Doc] -> Doc
vsep = vcat . intersperse (text "")

ppVernacular :: Vernacular -> String
ppVernacular = render . pp

instance Pp Vernacular where
  pp a = vsep [text "Module" <+> text (moduleName a) <> text "."
              , vsep (map pp (moduleDataTypes a))
              , vsep (map pp (moduleDefinitions a))
              , text "End" <+> text (moduleName a) <> text "."
              ]

instance Pp GallinaInductive where
  pp a = text "Inductive" <+> text (inductiveName a) <+> params <+> text ": Set :="
          $+$ nest 2 (vcat (map (\x -> text "|" <+> pp x) (inductiveConstrs a))
                      <> text ".")
    where params = if (not (null pars))
                   then lparen <+> hsep (map text pars) <+> text ": Set" <+> rparen
                   else empty
          pars = inductiveParams a

instance Pp GallinaConstructor where
  pp a = text (constrName a) <+> text ":" <+> pp (constrType a)

instance Pp GallinaDefinition where
  pp a = text "Definition" <+> text (defName a) 
         <+> ppDefType (defType a) <+> text ":="
         $$ nest 2 (pp (defBody a) <> text ".")
    where ppDefType (GallinaTyForall vars ty) = (if not (null vars)
                                                     then text "{" <+> hsep (map text vars)
                                                          <+> text ": Set" <+> text "}" 
                                                     else empty) <+> text ":" <+> pp ty
          ppDefType ty = text ":" <+> pp ty

instance Pp GallinaBody where
  pp (GallinaFunBody arity ms) = text "fun" 
                                 <+> hsep args
                                 <+> text "=>" 
                                 $$ nest 2 (text "match" <+> commas args <+> text "with" 
                                            $+$ nest 2 (vcat (map pp ms))
                                            $+$ text "end")
    where args = (map (\n -> text "x" <> text (show n)) [0 .. (arity - 1)])
  pp (GallinaPatBody t) = pp t

instance Pp GallinaMatch where
  pp a = text "|" <+> commas (map pp (matchPats a)) 
         <+> text "=>" <+> pp (matchTerm a)

instance Pp GallinaPat where
  ppPrec _ (GallinaPVar s) = text s
  ppPrec p (GallinaPApp s ps) = parensIf (p > 0 && not (null ps)) $ hsep (text s : map (ppPrec 1) ps)
  ppPrec _ GallinaPWildCard = text "_"

-- TODO: do something with vars in forall case.
instance Pp GallinaType where
  ppPrec p (GallinaTyForall _ ty) = parensIf (p > 0) $ pp ty
  ppPrec p (GallinaTyFun l r) = parensIf (p > 0) $ ppPrec 1 l <+> text "->" <+> pp r
  ppPrec p (GallinaTyApp l r) = parensIf (p > 1) $ pp l <+> ppPrec 2 r
  ppPrec _ (GallinaTyVar s) = text s
  ppPrec _ (GallinaTyCon s) = text s
  
instance Pp GallinaTerm where  
  ppPrec _ (GallinaVar s) = text s
  ppPrec p (GallinaApp l r) = parensIf (p > 1) $ pp l <+> ppPrec 2 r
  ppPrec p (GallinaLam v e) = parensIf (p > 1) $ text "fun" 
                              <+> hsep (map text v)
                              <+> text "=>"
                              <+> nest 2 (pp e)
  ppPrec _ (GallinaCase e ms) = text "match" <+> pp e <+> text "with" 
                                $+$ nest 2 (vcat (map pp ms))
                                $+$ text "end"

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

-- TODO: remove this, someday.
testDefinition :: GallinaDefinition
testDefinition = GallinaDefinition "const" (GallinaTyForall ["a", "b"] (GallinaTyFun (GallinaTyVar "a") (GallinaTyFun (GallinaTyVar "b") (GallinaTyVar "a")))) body
  where body = GallinaFunBody 2 [GallinaMatch [GallinaPVar "a", GallinaPVar "b"] (GallinaVar "a")]

