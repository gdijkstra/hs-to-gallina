import AG
import Gallina
import Language.Haskell.Exts
import System.Environment (getArgs)
import System.FilePath
import Data.Foldable

data Args = Args 
            { filePath :: FilePath
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
helpMessage = putStrLn "HsToGallina [-w [OUTFILE]] FILE\n\n  -w: write the output to a file. If OUTFILE is not given, then it will write to FILE with the extension replaced by \".v\""

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
