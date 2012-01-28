module Paths_softtyping (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName
  ) where

import Data.Version (Version(..))
import System.Environment (getEnv)

version :: Version
version = Version {versionBranch = [0,0,3], versionTags = []}

bindir, libdir, datadir, libexecdir :: FilePath

bindir     = "/Users/mabs/.cabal/bin"
libdir     = "/Users/mabs/.cabal/lib/softtyping-0.0.3/ghc-7.0.3"
datadir    = "/Users/mabs/.cabal/share/softtyping-0.0.3"
libexecdir = "/Users/mabs/.cabal/libexec"

getBinDir, getLibDir, getDataDir, getLibexecDir :: IO FilePath
getBinDir = catch (getEnv "softtyping_bindir") (\_ -> return bindir)
getLibDir = catch (getEnv "softtyping_libdir") (\_ -> return libdir)
getDataDir = catch (getEnv "softtyping_datadir") (\_ -> return datadir)
getLibexecDir = catch (getEnv "softtyping_libexecdir") (\_ -> return libexecdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
