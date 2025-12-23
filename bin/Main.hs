{-# LANGUAGE UnicodeSyntax #-}

import Cmd
import Ctx
import System.Environment
import Control.Monad (void)
import System.Directory (getCurrentDirectory)

main :: IO ()
main =
  do
    dir ← getCurrentDirectory
    putStrLn $ "Started Poett in directory " ++ show dir
    pargs ← getArgs
    case pargs of
      [] → repl
      _ → void $ mapM (flip processFile emptyCtx) pargs
      
