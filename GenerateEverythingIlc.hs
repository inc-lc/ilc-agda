{-# LANGUAGE PatternGuards #-}

-- TODO: this should actually be reusable by being a package.
-- And the parser should be an actual parser (ReadP? Whatever).
--
-- Could be combined with Toxaris/filter-agda-dependency-graph, since it needs
-- the output of this tool.

import qualified Data.List as List
import Control.Applicative
import System.Environment
import System.IO
import System.Exit
import System.FilePath
import System.FilePath.Find

--------------------------------------------------------------------------------
-- Configuration parameters
--------------------------------------------------------------------------------

marker           = "INCREMENTAL λ-CALCULUS"
projectName      = "Incremental λ-calculus"
binaryNameSuffix = "Ilc"
binaryName       = "GenerateEverything" ++ binaryNameSuffix

headerFile       = "EverythingHeader.agda.inc"
outputFile       = "Everything.agda"

-- This could be "src", as it was in the Agda standard library. But that change
-- might cause conflicts with other Agda work.
srcDir           = "."

--------------------------------------------------------------------------------
-- Logic to choose files to list - project-dependent
--------------------------------------------------------------------------------

-- Should we descend into this dir?
descendIntoDir = fileName /=? "bugs"

-- Do we want to exclude this source file
wantedSourceFile =
  fileName /=? "README.agda"

--------------------------------------------------------------------------------
-- Logic to choose files to list - should be project-independent
--------------------------------------------------------------------------------

isSource =
  fileName /=? outputFile &&?
  (extension ==? ".agda" ||? extension ==? ".lagda") &&?
  wantedSourceFile

sources = find descendIntoDir isSource srcDir

----------------------------------------
-- Reusable implementation
----------------------------------------

main = do
  args <- getArgs
  case args of
    [] -> return ()
    _  -> hPutStr stderr usage >> exitFailure

  header  <- readFileUTF8 headerFile
  modules <- filter isLibraryModule . List.sort <$> sources
  headers <- mapM extractHeader modules

  writeFileUTF8 outputFile $
    header ++ format (zip modules headers)

-- | Usage info.

usage :: String
usage = unlines
  [ binaryName ++ ": A utility program for Agda libraries (specialized for "
    ++ projectName ++ ")."
  , ""
  , "Usage: " ++ binaryName
  , ""
  , "This program should be run in the base directory of a clean checkout of"
  , "the library."
  , ""
  , "The program generates documentation for the library by extracting"
  , "headers from library modules. The output is written to " ++ outputFile
  , "with the file " ++ headerFile ++ " inserted verbatim at the beginning."
  ]

-- | Returns 'True' for all Agda files except for core modules.

isLibraryModule :: FilePath -> Bool
isLibraryModule f =
  takeExtension f `elem` [".agda", ".lagda"] &&
  dropExtension (takeFileName f) /= "Core"

-- | Reads a module and extracts the header.

extractHeader :: FilePath -> IO [String]
extractHeader mod = fmap (extract . lines) $ readFileUTF8 mod
  where
  delimiter = all (== '-')

  extract (d1 : expectedMarker : "--" : ss)
    | delimiter d1
    , expectedMarker == "-- " ++ marker
    , (info, d2 : rest) <- span ("-- " `List.isPrefixOf`) ss
    , delimiter d2
    = info
  extract _ = []

-- | Formats the extracted module information.

format :: [(FilePath, [String])]
          -- ^ Pairs of module names and headers. All lines in the
          -- headers are already prefixed with \"-- \".
       -> String
format = unlines . concat . map fmt
  where
  fmt (mod, header) = "" : header ++ ["import " ++ fileToMod mod]

-- | Translates a file name to the corresponding module name. It is
-- assumed that the file name corresponds to an Agda module under
-- 'srcDir'.

fileToMod :: FilePath -> String
fileToMod = map slashToDot . dropExtension . makeRelative srcDir
  where
  slashToDot c | isPathSeparator c = '.'
               | otherwise         = c

-- | A variant of 'readFile' which uses the 'utf8' encoding.

readFileUTF8 :: FilePath -> IO String
readFileUTF8 f = do
  h <- openFile f ReadMode
  hSetEncoding h utf8
  hGetContents h

-- | A variant of 'writeFile' which uses the 'utf8' encoding.

writeFileUTF8 :: FilePath -> String -> IO ()
writeFileUTF8 f s = withFile f WriteMode $ \h -> do
  hSetEncoding h utf8
  hPutStr h s
