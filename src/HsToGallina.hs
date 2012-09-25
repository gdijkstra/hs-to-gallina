import AG
import Control.Monad
import Gallina
import Language.Haskell.Exts
import System.Environment (getArgs)
import System.FilePath

data Args = Args 
            { filePath :: FilePath
            , write :: Bool
            }

parseArgs :: [String] -> Maybe Args
parseArgs [path] = Just $ Args { filePath = path, write = False }
parseArgs ["-w", path] = Just $ Args { filePath = path, write = True }
parseArgs _ = Nothing

helpMessage :: IO ()
helpMessage = putStrLn "HsToGallina <path>"

convertFile :: Args -> IO ()
convertFile args = do
  res <- parseFile . filePath $ args
  case res of
    ParseOk m -> do
      let output = ppVernacular . convertToGallina $ m
          fp = filePath args
      putStrLn output
      when (write args) (writeFile (replaceExtension fp ".v") output)
    ParseFailed _ _ -> putStrLn "convertFile: Parsing failed."

main :: IO ()
main = do
  as <- getArgs
  maybe helpMessage convertFile (parseArgs as)
