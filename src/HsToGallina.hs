-- | Main module. Parse command line arguments, parse the input file,
-- convert it to Coq code.
module Main where

import           AG                     (Result, resVernacular, convertToGallina)
import           BoveCapretta           (applyBoveCapretta)
import           Coinduction            (makeCoinductive)
import           Data.Foldable          (forM_)
import           Data.Maybe             (fromJust, fromMaybe, isNothing)
import           Gallina.PrettyPrinting
import           Gallina.Syntax
import           Language.Haskell.Exts
import           System.Console.GetOpt  (ArgDescr (..), ArgOrder (..),
                                         OptDescr (..), getOpt, usageInfo)
import           System.Environment     (getArgs)
import           System.FilePath

-- | Command line arguments data type.
data Args =
  Args
  { optShowVersion :: Bool -- ^ Show version number.
  , optCoqOutput   :: Maybe FilePath -- ^ The file to write the Coq output to.
  , optHsOutput    :: Maybe FilePath -- ^ The file to write the extracted Haskell code to.
  , optInput       :: Maybe FilePath -- ^ The Haskell file we will convert.
  }
  deriving Show

-- | Default command line arguments.
defaultArgs :: Args
defaultArgs = Args
  { optShowVersion = False
  , optCoqOutput   = Nothing
  , optHsOutput    = Nothing
  , optInput       = Nothing
  }

-- | Command line arguments descriptions.
options :: [OptDescr (Args -> Args)]
options =
 [ Option ['V','?'] ["version"]
   (NoArg (\opts -> opts { optShowVersion = True }))
   "show version number"
 , Option ['w'] ["write output to file"]
   (OptArg ((\f opts -> opts { optCoqOutput = f }))
    "FILE")
   "output FILE"
 , Option ['e'] ["extract"]
   (OptArg ((\f opts -> opts { optHsOutput = f }))
    "FILE")
   "output FILE"
 , Option ['f'] ["file"]
   (ReqArg ((\f opts -> opts { optInput = Just f }))
    "FILE")
   "input FILE"
 ]

-- | If the field 'optCoqOutput' is @Nothing@, then we will take the
-- 'optInput' path and change the extension to @\".v\"@.
addCoqOutput :: Args -> Args
addCoqOutput args = args { optCoqOutput = return . fromMaybe (replaceExtension inp ".v") $ cop }
  where
    inp = fromJust . optInput $ args
    cop = optCoqOutput args

-- | Parse the command line arguments. If the parsing fails, we will
-- return an error message, along with the usage message. Otherwise,
-- we will just return the result of the parsing.
parseArgs :: [String] -> Either String Args
parseArgs argv = fmap addCoqOutput $
   case getOpt Permute options argv of
      (o, _, []  ) -> checkResults $ foldl (flip id) defaultArgs o
      (_, _, errs) -> Left $ usage errs
  where
    usage errs = concat errs ++ usageInfo header options
    header = "Usage: HsToGallina -f FILE [OPTION...]"
    checkResults res | (isNothing . optInput $ res) && (not . optShowVersion $ res) = Left $ usage ["Error: HsToGallina requires -f FILE\n"]
                     | optShowVersion res = Left "HsToGallina, version 0.0.1"
                     | otherwise = Right res

-- | Add the appropriate implicit arguments commands before and after
-- theorem definitions and data type definitions.
addImplicitArgumentsCommands :: Result -> Result
addImplicitArgumentsCommands r = r { resVernacular = v { documentCommands = optimise . addCommands . documentCommands $ v } }
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

-- | Convert the file: parse the file, translate it to Gallina syntax
-- and apply the various transformations.
convertFile :: Args -> IO ()
convertFile args = do
  res <- parseFile . fromJust . optInput $ args
  case res of
    ParseOk m -> do
      let output = ppVernacularDocument
                   . resVernacular
                   . makeCoinductive
                   . addImplicitArgumentsCommands
                   . applyBoveCapretta
                   . convertToGallina
                   $ m
      forM_ (optCoqOutput args) (\outfp -> writeFile outfp output)
    ParseFailed _ _ -> putStrLn "convertFile: Parsing Haskell file failed."

-- | Main function.
main :: IO ()
main = do
  as <- getArgs
  either putStrLn convertFile $ parseArgs as
