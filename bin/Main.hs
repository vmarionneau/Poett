{-# LANGUAGE UnicodeSyntax #-}

import Cmd
import Ctx
import System.Environment
import Control.Monad (void)

main :: IO ()
main =
  do
    pargs ← getArgs
    case pargs of
      [] → repl
      _ → void $ mapM (flip processFile emptyCtx) pargs
      
