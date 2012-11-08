import           AG
import           BoveCapretta
import           Data.Foldable          (forM_)
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

addImplicitArgumentsCommands :: Vernacular -> Vernacular
addImplicitArgumentsCommands v = v { moduleDefinitions = optimise . addCommands . moduleDefinitions $ v }
  where
    addCommands = concatMap (\x -> if needsImplicit x
                                   then [GallinaSetImplicit, x, GallinaUnsetImplicit]
                                   else [x])
    needsImplicit (GallinaThmDef _   ) = True
    needsImplicit (GallinaInductive _) = True
    needsImplicit _                    = False
    optimise [] = []
    optimise (GallinaUnsetImplicit:GallinaSetImplicit:xs) = optimise xs
    optimise (x:xs) = x : optimise xs

convertFile :: Args -> IO ()
convertFile args = do
  res <- parseFile . filePath $ args
  case res of
    ParseOk m -> do
      let output = ppVernacular . addImplicitArgumentsCommands . uncurry applyBoveCapretta . convertToGallina $ m
      putStrLn output
      forM_ (writePath $ args) (\outfp -> writeFile outfp output)
    ParseFailed _ _ -> putStrLn "convertFile: Parsing Haskell file failed."

main :: IO ()
main = do
  as <- getArgs
  maybe helpMessage convertFile (parseArgs as)
