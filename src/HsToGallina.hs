import Language.Haskell.Exts
import System.Environment (getArgs)
import AG
import Gallina

data Args = Args 
            { filePath :: String
            }

parseArgs :: [String] -> Maybe Args
parseArgs [path] = Just (Args path)
parseArgs _ = Nothing

helpMessage :: IO ()
helpMessage = putStrLn "HsToGallina <path>"

convertFile :: Args -> IO ()
convertFile args = do
  res <- parseFile . filePath $ args
  case res of
    ParseOk m -> putStrLn . ppVernacular . convertToGallina $ m
    ParseFailed _ _ -> putStrLn "convertFile: Parsing failed."

main :: IO ()
main = do
  as <- getArgs
  maybe helpMessage convertFile (parseArgs as)
