import           AG
import           Data.Foldable
import           Gallina.PrettyPrinting
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

convertFile :: Args -> IO ()
convertFile args = do
  res <- parseFile . filePath $ args
  case res of
    ParseOk m -> do
      let output = ppVernacular . convertToGallina $ m
      putStrLn output
      forM_ (writePath $ args) (\outfp -> writeFile outfp output)
    ParseFailed _ _ -> putStrLn "convertFile: Parsing Haskell file failed."

main :: IO ()
main = do
  as <- getArgs
  maybe helpMessage convertFile (parseArgs as)
