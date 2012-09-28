module Gallina where

import Data.List
import Text.PrettyPrint.HughesPJ

data Vernacular = Vernacular { moduleName :: String 
                             , moduleDefinitions :: [GallinaDefinition]
                             }

data GallinaConstructor = GallinaConstructor { constrName :: String
                                             , constrType :: GallinaType
                                             }

data GallinaDefinition = GallinaInductive [GallinaInductiveBody]
                       | GallinaFunction { funArity :: Int
                                         , funName :: String
                                         , funType :: GallinaType
                                         , funBody :: GallinaTerm
                                         }
                       | GallinaPatBinding { patName :: String
                                           , patType :: GallinaType
                                           , patBody :: GallinaTerm
                                           } 
                       | GallinaFixpoint [GallinaDefinition] 

data GallinaInductiveBody = GallinaInductiveBody { inductiveName :: String
                                                 , inductiveParams :: [String]
                                                 , inductiveConstrs :: [GallinaConstructor] }

data GallinaFixpointBody = GallinaFixpointBody { fixName :: String
                                               , fixType :: GallinaType
                                               , fixBody :: GallinaTerm
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
     | GallinaTyApp GallinaType GallinaType        
     | GallinaTyVar String
     | GallinaTyCon String

data GallinaTerm = GallinaVar String
                 | GallinaApp GallinaTerm GallinaTerm
                 | GallinaLam [String] GallinaTerm
                 | GallinaCase [GallinaTerm] [GallinaMatch]

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
              , vsep (map pp (moduleDefinitions a))
              , text "End" <+> text (moduleName a) <> text "."
              ]

instance Pp GallinaConstructor where
  pp a = text (constrName a) <+> text ":" <+> pp (constrType a)

instance Pp GallinaDefinition where
  pp (GallinaInductive is) = text "Inductive" <+> vsep (intersperse (text "with") . map ppBody $ is) <> text "."
    where params a = if (not (null (pars a)))
                   then lparen <+> hsep (map text (pars a)) <+> text ": Set" <+> rparen
                   else empty
          pars a = inductiveParams a
          ppBody a = text (inductiveName a) <+> params a <+> text ": Set :="
                     $+$ nest 2 (vcat (map (\x -> text "|" <+> pp x) (inductiveConstrs a)))


  pp (GallinaFunction a n t b)= text "Definition" <+> text n
         <+> ppFreeVars <+> ppArgs <+> text ":" <+> ppRes <+> text ":="
         $$ nest 2 (pp b <> text ".")
    where ppFreeVars = if not (null freeVars)
                       then text "{" <+> hsep (map text freeVars)
                            <+> text ": Set" <+> text "}" 
                       else empty
          ppArgs = hsep
                   $ map (\(arg, no) -> parens (text ('x' : show no) 
                                              <+> text ":" 
                                              <+> pp arg))
                   $ zip args ([0..] :: [Int])
          ppRes = pp res
          freeVars = case t of
            (GallinaTyForall vars _) -> vars
            _ -> []
          flat (GallinaTyForall _ ty) = flat ty
          flat (GallinaTyFun l r) = l : flat r
          flat ty@(GallinaTyApp _ _) = [ty]
          flat ty@(GallinaTyVar _) = [ty]
          flat ty@(GallinaTyCon _) = [ty]
          unflat [] = error "unflat: empty list"
          unflat [x] = x
          unflat (x:xs) = GallinaTyFun x (unflat xs)
          (args, res) = (take a (flat t), unflat $ drop a (flat t))
  pp (GallinaPatBinding n t b)= text "Definition" <+> text n <+> ppFreeVars <+> text ":" 
                                <+> pp t <+> text ":="
                                $$ nest 2 (pp b <> text ".")
    where ppFreeVars = if not (null freeVars)
                       then text "{" <+> hsep (map text freeVars)
                            <+> text ": Set" <+> text "}" 
                       else empty
          freeVars = case t of
            (GallinaTyForall vars _) -> vars
            _ -> []


  pp (GallinaFixpoint is)= text "Fixpoint" <+> vsep (intersperse (text "with") . map ppBody $ is) <> text "."
    where ppBody (GallinaFunction a n t b) = text n <+> ppFreeVars <+> ppArgs <+> text ":" <+> ppRes <+> text ":="
                                           $$ nest 2 (pp b)
            where ppFreeVars = if not (null freeVars)
                               then text "{" <+> hsep (map text freeVars)
                                    <+> text ": Set" <+> text "}" 
                               else empty
                  ppArgs = hsep
                           $ map (\(arg, no) -> parens (text ('x' : show no) 
                                                        <+> text ":" 
                                                        <+> pp arg))
                           $ zip args ([0..] :: [Int])
                  ppRes = pp res
                  freeVars = case t of
                    (GallinaTyForall vars _) -> vars
                    _ -> []
                  flat (GallinaTyForall _ ty) = flat ty
                  flat (GallinaTyFun l r) = l : flat r
                  flat ty@(GallinaTyApp _ _) = [ty]
                  flat ty@(GallinaTyVar _) = [ty]
                  flat ty@(GallinaTyCon _) = [ty]
                  unflat [] = error "unflat: empty list"
                  unflat [x] = x
                  unflat (x:xs) = GallinaTyFun x (unflat xs)
                  (args, res) = (take a (flat t), unflat $ drop a (flat t))
          ppBody (GallinaPatBinding n t b) = text n <+> text ":" <+> pp t <+> text ":="
                                             $$ nest 2 (pp b)
          ppBody _ = error "pp GallinaFixpoint: meh"

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
  ppPrec _ (GallinaCase e ms) = text "match" <+> commas (map pp e) <+> text "with" 
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

