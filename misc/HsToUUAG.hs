-- Small throwaway program to convert Haskell data type descriptions
-- to UUAG descriptions. Note that the result will probably still need
-- manual adjustments. It will generate some fields with the type
-- between curly braces, with a useless, malformed name. Note that is
-- also doesn't work with C preprocessor directives.

import Language.Haskell.Exts
import Data.List
import Data.Char
import System.Environment (getArgs)

data Args = Args { filePath :: String }

parseArgs :: [String] -> Maybe Args
parseArgs [path] = Just (Args path)
parseArgs _ = Nothing

helpMessage :: IO ()
helpMessage = putStrLn "HsToUUAG <path>"

convertFile :: Args -> IO ()
convertFile args = do
  res <- parseFile (filePath args)
  case res of
    ParseOk a -> putStrLn . fetchDataDecls $ a
    ParseFailed _ _ -> putStrLn "convertFile: Parsing failed."

decls :: Module -> [Decl]
decls (Module _ _ _ _ _ _ d) = d

nameToStr :: Name -> String
nameToStr = prettyPrint

isDataDecl :: Decl -> Bool
isDataDecl (DataDecl _ _ _ _ _ _ _) = True
isDataDecl _ = False

-- data decls and all the type decls needed
declToStr :: Decl -> (String, [String])
declToStr (DataDecl _ _ _ name tyvars cons derive) = 
  let (consStrs, typeStrs) = constructorsToStr cons
  in   ("data " ++ prettyPrint name
--        ++ "\nTyVars: " ++ tyVarsToStr tyvars
        ++ consStrs
        ++ "\n\nderiving " ++ prettyPrint name ++ " : " ++ derivingsToStr derive
        , concat typeStrs)
declToStr _ = error "declToStr: This should not happen."

constructorsToStr :: [QualConDecl] -> (String, [[String]])
constructorsToStr f = ((++) "\n\t| " . intercalate "\n\t| " . map (fst . constructorToStr) $ f, nub . map (snd . constructorToStr) $ f)
  where
    constructorToStr :: QualConDecl -> (String, [String])
    constructorToStr (QualConDecl _ [] [] conDecl) = conDeclToStr conDecl
    constructorToStr _ = error "constructorToStr: Don't do this."
    conDeclToStr (ConDecl name args) = (prettyPrint name ++ "\t " ++ intercalate " " (makeFieldNames (map ignoreBang args)), makeTypeSynonyms . map ignoreBang$ args)
    conDeclToStr (RecDecl name fields) = (prettyPrint name ++ "\t " ++ intercalate " " (makeRecordFieldNames fields), makeTypeSynonyms . map (ignoreBang . snd) $ fields)
    conDeclToStr (InfixConDecl l name r) = error "conDeclToStr: infix declarations not supported"

ignoreBang :: BangType -> Type
ignoreBang (BangedTy t) = t
ignoreBang (UnBangedTy t) = t
ignoreBang (UnpackedTy t) = t
    
lowercase :: String -> String
lowercase = map toLower
    
makeRecordFieldNames :: [([Name], BangType)] -> [String]
makeRecordFieldNames = concatMap (\(names, bty) -> map (makeRecordFieldName bty) names)
  where
    makeRecordFieldName bty name = prettyPrint name ++ " :: " ++ flattenTy (ignoreBang bty)

makeTypeSynonyms :: [Type] -> [String]
makeTypeSynonyms = nub . map makeTypeSynonym . filter isMaybeOrList . map unParen
  where
    unParen (TyParen ty) = ty
    unParen ty = ty
    isMaybeOrList (TyApp l _) = l == TyCon (UnQual (Ident "Maybe"))
    isMaybeOrList (TyList _) = True
    isMaybeOrList _ = False
    makeTypeSynonym ty = "type " ++ flattenTy ty ++ " = " ++ prettyPrint ty

makeFieldNames :: [Type] -> [String]
makeFieldNames tys = reverse . snd . foldr f ([], []) . reverse $ tys
  where
    f ty (table, fieldNames) = case lookup (flattenTy ty) table of
      Nothing -> ((flattenTy ty, 0):table, makeFieldName ty 0 : fieldNames)
      (Just c) -> ((flattenTy ty, c+1):table, makeFieldName ty (c+1) : fieldNames)
    makeFieldName ty 0 = lowercase (flattenTy ty) ++ " :: " ++ flattenTy ty
    makeFieldName ty c = lowercase (flattenTy ty) ++ show c ++ " :: " ++ flattenTy ty

flattenTy :: Type -> String
flattenTy (TyList ty) = flattenTy ty ++ "s"
flattenTy (TyApp l r) = if l == TyCon (UnQual (Ident "Maybe"))
                        then flattenTy r ++ "Opt"
                        else error "flattenTy: no other type applications other than Maybe supported"
flattenTy (TyVar n) = prettyPrint n
flattenTy (TyCon n) = prettyPrint n
flattenTy (TyParen ty) = "(" ++ flattenTy ty ++ ")"
flattenTy ty = "{" ++ prettyPrint ty ++ "}" -- these need to be looked at manually
-- flattenTy (TyInfix _ _ _) = error "flattenTy: don't use infix"
-- flattenTy (TyKind _ _) = error "flattenTy: kind annotations not supported"
-- flattenTy (TyForall _ _ _) = error "flattenTy: forall not supported"
-- flattenTy (TyFun _ _) = error "flattenTy: function types not supported"
-- flattenTy (TyTuple _ _) = error "flattenTy: tuples not supported"
    
-- Ignore kind annotations.
tyVarsToStr :: [TyVarBind] -> String
tyVarsToStr = intercalate " " . map tyVarsToStr
  where
    tyVarsToStr (KindedVar n _) = prettyPrint n
    tyVarsToStr (UnkindedVar n) = prettyPrint n

derivingsToStr :: [(QName, [t])] -> String
derivingsToStr = intercalate ", " . map derivingToStr
  where
    derivingToStr (name, []) = prettyPrint name
    derivingToStr (_, (_:_)) = error "derivingToStr: MPTC not supported."

fetchDataDecls :: Module -> String
fetchDataDecls m = dataDecls ++ "\n\n" ++ typeDecls
  where
    res = unzip . map declToStr . filter isDataDecl . decls $ m
    dataDecls = intercalate "\n\n\n" . fst $ res
    typeDecls = intercalate "\n" . nub . concat . snd $ res

main :: IO ()
main = do
  as <- getArgs
  maybe helpMessage convertFile (parseArgs as)
