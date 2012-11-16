-- | Main module. Parse command line arguments, parse the input file,
-- convert it to Coq code.
module Main where

import           AG
import           BoveCapretta
import           Data.Foldable          (forM_)
import           Data.Maybe             (fromJust, fromMaybe, isNothing)
import qualified Data.Set               as S
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
      (o, _, []  ) -> let res = foldl (flip id) defaultArgs o
                    in if (isNothing . optInput $ res) && (not . optShowVersion $ res)
                       then Left $ usage ["Error: HsToGallina requires -f FILE\n"]
                       else Right res
      (_, _, errs) -> Left $ usage errs
  where
    usage errs = concat errs ++ usageInfo header options
    header = "Usage: HsToGallina -f FILE [OPTION...]"

-- | Change the fixpoints to cofixpoints for the definitions as
-- specified by the pragmas. Note that we will only change the
-- definitions if all definitions of a mutually recursive group should
-- be read coinductively. We will raise an error otherwise.
makeCoinductive :: Result -> Result
makeCoinductive r = r { resVernacular = v { documentCommands = newDefinitions } }
  where
    v = resVernacular r
    coDefs = coDefinitions r
    oldDefs = documentCommands v
    fixName (Left b) = funName b
    fixName (Right b) = patName b
    newDefinitions = map adaptDefinition oldDefs
    adaptDefinition (GallinaInductive is _) = case allOrNothing (flip S.member coDefs) . map inductiveName $ is of
      Just b -> GallinaInductive is b
      Nothing -> error "makeCoinductive: error."
    adaptDefinition (GallinaFixpoint is _) = case allOrNothing (flip S.member coDefs) . map fixName $ is of
      Just b -> GallinaFixpoint is b
      Nothing -> error "makeCoinductive: error."
    adaptDefinition d = d

-- | Check whether the predicate holds for all elements of the list,
-- or doesn't hold for all the elements of the list. If there's an odd
-- one out, we will return @Nothing@. Otherwise, we will return @Just
-- b@, where @b@ indicates whether the predicate holds for every
-- element of the list. An empty list will yield @Just True@ as a
-- result.
allOrNothing :: (a -> Bool) -> [a] -> Maybe Bool
allOrNothing _ [] = Just True
allOrNothing p xs = foldr1 iff . map (Just . p) $ xs
  where
    iff (Just True) (Just True) = Just True
    iff (Just False) (Just False) = Just False
    iff _ _ = Nothing

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
