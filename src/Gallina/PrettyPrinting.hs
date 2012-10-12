module Gallina.PrettyPrinting where

import           Data.List
import           Gallina.Syntax
import           Text.PrettyPrint

class Pp a where
  pp     :: a -> Doc
  ppPrec :: Int -> a -> Doc

  pp       = ppPrec 0
  ppPrec _ = pp

parensIf :: Bool -> Doc -> Doc
parensIf b = if b then parens else id

commas :: [Doc] -> Doc
commas = hsep . intersperse (text ",")

vsep :: [Doc] -> Doc
vsep = vcat . intersperse (text "")

ppVernacular :: Vernacular -> String
ppVernacular = render . pp

ppGroup :: (Pp a) => String -> [a] -> Doc
ppGroup name is = text name <+> vsep (intersperse (text "with") . map pp $ is)

ppGroupDotted :: (Pp a) => String -> [a] -> Doc
ppGroupDotted name is = ppGroup name is <> text "."


instance Pp Vernacular where
  pp a = vsep [text "Module" <+> text (moduleName a) <> text "."
              , text "Set Implicit Arguments."
              , text "Set Contextual Implicit."
              , vsep (map pp (moduleDefinitions a))
              , text "End" <+> text (moduleName a) <> text "."
              ]


instance Pp GallinaUngroupedDefinition where
  pp a = text "Ungrouped" <> pp a

instance Pp GallinaDefinition where
  pp (GallinaInductive is ) = ppGroupDotted "Inductive" is
  pp (GallinaFixpoint is  ) = ppGroupDotted "Fixpoint" is
  pp (GallinaFunction b   ) = ppGroupDotted "Definition" [b]
  pp (GallinaPatBinding b ) = ppGroupDotted "Definition" [b]

instance Pp GallinaLetDefinition where
  pp (GallinaLetFixpoint b   ) = ppGroup "fix" [b]
  pp (GallinaLetFunction b   ) = ppGroup "" [b]
  pp (GallinaLetPatBinding b ) = ppGroup "" [b]

instance Pp GallinaInductiveBody where
  pp a = hsep [ text (inductiveName a)
              , params
              , text ": Set :="
                $+$
                nest 2 (vcat (map (\x -> text "|" <+> pp x) (inductiveConstrs a)))
              ]
    where
      params = if not (null pars)
               then hsep [lparen, hsep (map text pars), text ": Set", rparen]
               else empty
      pars   = inductiveParams a

instance Pp GallinaConstructor where
  pp a = hsep [ text (constrName a)
              , text ":"
              , pp (constrType a)
              ]

ppArg :: (Pp a) => Maybe a -> Int -> Doc
ppArg Nothing  no = text ('x' : show no)
ppArg (Just t) no = parens . hsep $ [text ('x' : show no), text ":", pp t]

instance Pp GallinaFunctionBody where
  pp (GallinaFunctionBody a n t b) = hsep [ text n
                                          , ppFreeVars
                                          , ppArgs
                                          , maybe empty ((text ":" <+>) . pp) res
                                          , text ":="
                                          ]
                                     $$ nest 2 (pp b)
    where
      ppFreeVars = if not (null freeVars)
                   then hsep [ text "{"
                             , hsep (map text freeVars)
                             , text ": Set"
                             , text "}"
                             ]
                   else empty
      ppArgs = hsep
               $ map (\(arg, no) -> ppArg arg no)
               $ zip args ([0..] :: [Int])
      freeVars = case t of
        (Just (GallinaTyForall vars _)) -> vars
        _ -> []
      flat (GallinaTyForall _ ty ) = flat ty
      flat (GallinaTyFun l r     ) = l : flat r
      flat ty@(GallinaTyApp _ _  ) = [ty]
      flat ty@(GallinaTyVar _    ) = [ty]
      flat ty@(GallinaTyCon _    ) = [ty]
      unflat []     = Nothing
      unflat [x]    = Just x
      unflat (x:xs) = do
        uxs <- unflat xs
        return $ GallinaTyFun x uxs
      (args, res) = case t of
        Nothing -> (replicate a Nothing, Nothing)
        Just x -> (map Just $ take a (flat x), unflat $ drop a (flat x))

instance Pp GallinaPatBindingBody where
  pp (GallinaPatBindingBody n t b) = hsep [ text n
                                          , ppFreeVars
                                          , maybe empty ((text ":" <+>) . pp) t
                                          , text ":="
                                          ]
                                     $$ nest 2 (pp b)
    where
      ppFreeVars = if not (null freeVars)
                   then hsep [ text "{"
                             , hsep (map text freeVars)
                             , text ": Set"
                             , text "}"
                             ]
                   else empty
      freeVars = case t of
        (Just (GallinaTyForall vars _)) -> vars
        _ -> []

instance (Pp a, Pp b) => Pp (Either a b) where
  pp (Left a  ) = pp a
  pp (Right a ) = pp a

instance Pp GallinaMatch where
  pp a = text "|" <+> commas (map pp (matchPats a))
         <+> text "=>" <+> pp (matchTerm a)

instance Pp GallinaPat where
  ppPrec _ (GallinaPVar s    ) = text s
  ppPrec p (GallinaPApp s ps ) = parensIf (p > 0 && not (null ps)) $ hsep (text s : map (ppPrec 1) ps)
  ppPrec _ GallinaPWildCard    = text "_"

instance Pp GallinaType where
  ppPrec _ (GallinaTyForall _ _ ) = error "ppPrec: foralls should not occur here."
  ppPrec p (GallinaTyFun l r    ) = parensIf (p > 0) $ ppPrec 1 l <+> text "->" <+> pp r
  ppPrec p (GallinaTyApp l r    ) = parensIf (p > 1) $ pp l <+> ppPrec 2 r
  ppPrec _ (GallinaTyVar s      ) = text s
  ppPrec _ (GallinaTyCon s      ) = text s

instance Pp GallinaTerm where
  ppPrec _ (GallinaVar s     ) = text s
  ppPrec p (GallinaApp l r   ) = parensIf (p > 1) $ pp l <+> ppPrec 2 r
  ppPrec p (GallinaLam v e   ) = parensIf (p > 1) $ text "fun"
                                 <+> hsep (map text v)
                                 <+> text "=>"
                                 <+> nest 2 (pp e)
  ppPrec _ (GallinaCase e ms ) = text "match" <+> commas (map pp e) <+> text "with"
                                 $+$ nest 2 (vcat (map pp ms))
                                 $+$ text "end"
  ppPrec _ (GallinaLet ds e  ) = foldr (\x y -> text "let" <+> pp x $+$ text "in" <+> y) (pp e) ds
  ppPrec _ (GallinaIf c t f  ) = sep [ text "if", pp c
                                     , text "then", pp t
                                     , text "else", pp f
                                     ]
