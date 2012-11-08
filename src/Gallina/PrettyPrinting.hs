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
ppGroup name is = text name <+> vcat (intersperse (text "with") . map pp $ is)

ppGroupDotted :: (Pp a) => String -> [a] -> Doc
ppGroupDotted name is = ppGroup name is <> text "."


instance Pp Vernacular where
  pp a = vsep [text "Module" <+> text (moduleName a) <> text "."
              , text "Set Contextual Implicit."
              , vsep (map pp (moduleDefinitions a))
              , text "End" <+> text (moduleName a) <> text "."
              ]


instance Pp GallinaUngroupedDefinition where
  pp a = text "Ungrouped" <> pp a

instance Pp GallinaDefinition where
  pp (GallinaInductive is) = ppGroupDotted "Inductive" is
  pp (GallinaFixpoint is ) = ppGroupDotted "Fixpoint" is
  pp (GallinaFunction b  ) = ppGroupDotted "Definition" [b]
  pp (GallinaPatBinding b) = ppGroupDotted "Definition" [b]
  pp (GallinaThmDef d    ) = pp d
  pp GallinaSetImplicit    = text "Set Implicit Arguments."
  pp GallinaUnsetImplicit  = text "Unset Implicit Arguments."


instance Pp GallinaLetDefinition where
  pp (GallinaLetFixpoint b   ) = ppGroup "fix" [b]
  pp (GallinaLetFunction b   ) = ppGroup "" [b]
  pp (GallinaLetPatBinding b ) = ppGroup "" [b]

instance Pp GallinaInductiveBody where
  pp a = hsep [ text (inductiveName a)
              , params
              , text ":"
              , pp (inductiveType a)
              , text ":="
              ]
         $$
         vcat (map (\x -> text "|" <+> pp x) (inductiveConstrs a))

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
      (args, res) = case t of
        Nothing -> (replicate a Nothing, Nothing)
        Just x -> (\(as,r) -> (map Just as, Just r)) (argsResTy a x)

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
  ppPrec p (GallinaTyForall s ty) = parensIf (p > 0) $ hsep [text "forall", hsep . map text $ s, text ",", pp ty]
  ppPrec p (GallinaTyFun l r    ) = parensIf (p > 0) $ ppPrec 1 l <+> text "->" <+> pp r
  ppPrec p (GallinaTyApp l r    ) = parensIf (p > 1) $ pp l <+> ppPrec 2 r
  ppPrec _ (GallinaTyVar s      ) = text s
  ppPrec _ (GallinaTyCon s      ) = text s
  ppPrec _ (GallinaTySet        ) = text "Set"
  ppPrec p (GallinaTyPi st t1   ) = parensIf (p > 0) $ hsep [ text "forall"
                                                            , hsep
                                                              . map (\(s,t) -> parens (hsep [text s, text ":", pp t]))
                                                              $ st
                                                            , text ","
                                                            , pp t1
                                                            ]
  ppPrec p (GallinaTyEq t1 t2   ) = parensIf (p > 0) $ hsep [ pp t1
                                                            , text "="
                                                            , pp t2
                                                            ]

instance Pp GallinaTerm where
  ppPrec _ (GallinaVar s        ) = text s
  ppPrec p (GallinaApp l r      ) = parensIf (p > 1) $ pp l <+> ppPrec 2 r
  ppPrec p (GallinaLam v e      ) = parensIf (p > 1) $ text "fun"
                                    <+> hsep (map text v)
                                    <+> text "=>"
                                    <+> nest 2 (pp e)
  ppPrec _ (GallinaCase e ms    ) = text "match" <+> commas (map pp e) <+> text "with"
                                    $$ nest 2 (vcat (map pp ms))
                                    $$ text "end"
  ppPrec _ (GallinaDepCase e r m) = hsep
                                    [ text "match"
                                    , commas (map (\(t,v) -> pp t <+> text "as" <+> text v) e)
                                    , text "return"
                                    , pp r
                                    , text "with"
                                    ]
                                    $$ nest 2 (vcat (map pp m))
                                    $$ text "end"
  ppPrec _ (GallinaLet ds e     ) = foldr (\x y -> text "let" <+> pp x $$ text "in" <+> y) (pp e) ds
  ppPrec _ (GallinaIf c t f     ) = sep [ text "if", pp c
                                        , text "then", pp t
                                        , text "else", pp f
                                        ]
  ppPrec _ (GallinaTyTerm ty    ) = ppPrec 2 ty

instance Pp GallinaTheorem where
  ppPrec _ thm = vcat [ hsep [ text "Theorem"
                             , text (theoremName thm)
                             , text ":", pp (theoremProp thm)
                             , text "."
                             ]
                      , text (theoremProof thm)
                      , text "Defined."
                      ]
