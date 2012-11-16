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

data Args =
  Args
  { optShowVersion :: Bool
  , optCoqOutput   :: Maybe FilePath
  , optHsOutput    :: Maybe FilePath
  , optInput       :: Maybe FilePath
  }
  deriving Show

defaultArgs :: Args
defaultArgs = Args
  { optShowVersion = False
  , optCoqOutput   = Nothing
  , optHsOutput    = Nothing
  , optInput       = Nothing
  }

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

addCoqOutput :: Args -> Args
addCoqOutput args = args { optCoqOutput = return . fromMaybe (replaceExtension inp ".v") $ cop }
  where
    inp = fromJust . optInput $ args
    cop = optCoqOutput args

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
  res <- parseFile . fromJust . optInput $ args
  case res of
    ParseOk m -> do
      let output = ppVernacular
                   . resVernacular
                   . makeCoinductive
                   . addImplicitArgumentsCommands
                   . applyBoveCapretta
                   . convertToGallina
                   $ m
      forM_ (optCoqOutput args) (\outfp -> writeFile outfp output)
    ParseFailed _ _ -> putStrLn "convertFile: Parsing Haskell file failed."

main :: IO ()
main = do
  as <- getArgs
  either putStrLn convertFile $ parseArgs as
