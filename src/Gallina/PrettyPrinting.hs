-- | Pretty printer for Gallina code and Coq VernacularDocument commands.
module Gallina.PrettyPrinting where

import           Data.List        (intersperse)
import           Gallina.Syntax
import           Text.PrettyPrint

-- | Pretty printing class.
class Pp a where
  pp     :: a -> Doc       -- ^ Pretty print something.
  ppPrec :: Int -> a -> Doc -- ^ Pretty print according to the precedence context given.

  pp       = ppPrec 0
  ppPrec _ = pp

-- | Enclose something in parentheses if the boolean value equals @True@.
parensIf :: Bool -> Doc -> Doc
parensIf b = if b then parens else id

-- | Intersperse commas and concatenate the result horizontally.
commas :: [Doc] -> Doc
commas = hcat . intersperse (text ", ")

-- | Concatenate the elements of the list vertically with an empty
-- line separating every element.
vsep :: [Doc] -> Doc
vsep = vcat . intersperse (text "")

-- | Pretty print the whole 'VernacularDocument' document and render the
-- result to a 'String'.
ppVernacularDocument :: VernacularDocument -> String
ppVernacularDocument = render . pp

-- | Group a bunch of definitions and intersperse them with the
-- keyword @\"with\"@. Used for mutually recursive definitions.
ppGroupDotted :: (Pp a) => String -> [a] -> Doc
ppGroupDotted name is = text name <+> vcat (intersperse (text "with") . map pp $ is) <> char '.'

instance Pp VernacularDocument where
  pp a = vsep [text "Module" <+> text (documentName a) <> char '.'
              , text "Require Import Prelude."
              , text "Set Contextual Implicit."
              , vsep (map pp (documentCommands a))
              , text "End" <+> text (documentName a) <> char '.'
              , text "Extraction \"extracted/" <> text (documentName a) <> text ".hs\" " <> text (documentName a) <> char '.'
              ]

instance Pp VernacularCommand where
  pp (GallinaInductive is False ) = ppGroupDotted "Inductive" is
  pp (GallinaInductive is True  ) = ppGroupDotted "CoInductive" is
  pp (GallinaFixpoint is False  ) = ppGroupDotted "Fixpoint" is
  pp (GallinaFixpoint is True   ) = ppGroupDotted "CoFixpoint" is
  pp (GallinaTypeSynonym b      ) = ppGroupDotted "Definition" [b]
  pp (GallinaFunction b         ) = ppGroupDotted "Definition" [b]
  pp (GallinaPatBinding b       ) = ppGroupDotted "Definition" [b]
  pp (GallinaThmDef d           ) = pp d
  pp GallinaSetImplicit           = text "Set Implicit Arguments."
  pp GallinaUnsetImplicit         = text "Unset Implicit Arguments."

instance Pp GallinaTypeSynBody where
  pp a = hsep [ text (synonymName a)
              , params
              , text ":"
              , pp GallinaTySet
              , text ":="
              ]
         <+>
         pp (synonymType a)

    where
      params = if not (null pars)
               then hsep [lparen, hsep (map text pars), text ": Set", rparen]
               else empty
      pars   = synonymParams a

instance Pp GallinaLetDefinition where
  pp (GallinaLetFixpoint b   ) = text "fix" <+> pp b
  pp (GallinaLetFunction b   ) = pp b
  pp (GallinaLetPatBinding b ) = pp b

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

-- | Print an argument with its number and, optionally its type as
-- well.
ppArg :: Maybe GallinaType -> Int -> Doc
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
  ppPrec _ (GallinaTyProp       ) = text "Prop"
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
  ppPrec p (GallinaTyList t     ) = parensIf (p > 1) $ text "List" <+> ppPrec 2 t
  ppPrec p (GallinaTyTerm t     ) = ppPrec p t

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
  ppPrec _ (GallinaTermTy ty    ) = ppPrec 2 ty
  ppPrec _ (GallinaList []      ) = text "nil"
  ppPrec _ (GallinaList ts      ) = char '[' <> (hcat . intersperse (text ", ") . map pp $ ts) <> char ']'

instance Pp GallinaTheorem where
  ppPrec _ thm = vcat [ hsep [ text "Theorem"
                             , text (theoremName thm)
                             , text ":", pp (theoremProp thm)
                             , char '.'
                             ]
                      , text (theoremProof thm)
                      , text "Defined."
                      ]
