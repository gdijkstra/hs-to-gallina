import           AG
import           BoveCapretta
import           Data.Foldable          (forM_)
import qualified Data.Set               as S
import           Gallina.PrettyPrinting
import           Gallina.Syntax
import           Language.Haskell.Exts
import           System.Environment     (getArgs)
import           System.FilePath

data Args =
  Args { filePath  :: FilePath
       , writePath :: Maybe FilePath
       }

parseArgs :: [String] -> Maybe Args
parseArgs [fp] = Just $ Args { filePath = fp, writePath = Nothing }
parseArgs ["-w", fp] = Just $ Args { filePath = fp
                                   , writePath = Just (replaceExtension fp ".v")
                                   }
parseArgs ["-w", outfp, fp] = Just $ Args { filePath = fp, writePath = Just outfp }
parseArgs _ = Nothing

helpMessage :: IO ()
helpMessage = do
  putStrLn "HsToGallina [-w [OUTFILE]] FILE"
  putStrLn "  -w: write the output to a file. If OUTFILE is not given, then"
  putStrLn "      it will write to FILE with the extension replaced by \".v\""

makeCoinductive :: Result -> Result
makeCoinductive r = r { resVernacular = v { moduleDefinitions = newDefinitions } }
  where
    v = resVernacular r
    coDefs = coDefinitions r
    oldDefs = moduleDefinitions v
    fixName (Left b) = funName b
    fixName (Right b) = patName b
    newDefinitions = map adaptDefinition oldDefs
    adaptDefinition (GallinaInductive is _) = case allOrNothing (flip S.member coDefs) . map inductiveName $ is of
      Just b -> GallinaInductive is b
      Nothing -> error "makeCoinductive: error."
    adaptDefinition (GallinaFixpoint is _) = case allOrNothing (flip S.member coDefs) . map fixName $ is of
      Just b -> GallinaFixpoint is b
      Nothing -> error "makeCoinductive: error."
    adaptDefinition b = b

allOrNothing :: (a -> Bool) -> [a] -> Maybe Bool
allOrNothing p = foldr1 iff . map (Just . p)
  where
    iff (Just True) (Just True) = Just True
    iff (Just False) (Just False) = Just False
    iff _ _ = Nothing

addImplicitArgumentsCommands :: Result -> Result
addImplicitArgumentsCommands r = r { resVernacular = v { moduleDefinitions = optimise . addCommands . moduleDefinitions $ v } }
  where
    v = resVernacular r
    addCommands = concatMap (\x -> if needsImplicit x
                                   then [GallinaSetImplicit, x, GallinaUnsetImplicit]
                                   else [x])
    needsImplicit (GallinaThmDef _   ) = True
    needsImplicit (GallinaInductive _ _) = True
    needsImplicit _                    = False
    optimise [] = []
    optimise (GallinaUnsetImplicit:GallinaSetImplicit:xs) = optimise xs
    optimise (x:xs) = x : optimise xs

convertFile :: Args -> IO ()
convertFile args = do
  res <- parseFile . filePath $ args
  case res of
    ParseOk m -> do
      let output = ppVernacular . resVernacular . makeCoinductive . addImplicitArgumentsCommands . applyBoveCapretta . convertToGallina $ m
      putStrLn output
      forM_ (writePath $ args) (\outfp -> writeFile outfp output)
    ParseFailed _ _ -> putStrLn "convertFile: Parsing Haskell file failed."

main :: IO ()
main = do
  as <- getArgs
  maybe helpMessage convertFile (parseArgs as)
