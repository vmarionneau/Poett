{-# LANGUAGE UnicodeSyntax #-}

import Parser
import Cmd
import Ctx
import System.Environment
import System.IO (isEOF)
import Control.Monad (void)

processInput :: String → Ctx → IO Ctx
processInput input ctx =
  do
    let inctx =
          do
            { (toks, rest) ← inCtxOfMaybe "Lexing failed" $ runParser lexer $ Stream input 0 0
            ; (cmds, rest') ← inCtxOfMaybe "Parsing failed" $ runParser script $ Scoped toks []
            ; if (streamData rest) /= []
              then fail $ "Lexer error at :" ++ show (streamRow rest, streamCol rest)
              else
                case (scopedData rest') of
                  h:_ → fail $ "Parser error at : " ++ show (pos h)
                  [] → mapM processCommand (locData <$> cmds)
            }
    case runInCtx inctx ctx of
      Left msg → putStrLn msg >> pure ctx
      Right (ctx', action) → mapM id action >> pure ctx'

processFile :: String → IO ()
processFile fileName =
  do
    file ← readFile fileName
    void $ processInput file emptyCtx

repl :: IO ()
repl = aux [] emptyCtx
  where
    aux ls ctx =
      do
        end ← isEOF
        if end
          then void $ processInput (unlines ls) ctx 
          else
          do
            { l ← getLine
            ; if l == []
              then
                do ctx' ← processInput (unlines ls) ctx
                   aux [] ctx'
              else aux (ls ++ [l]) ctx
            }

main :: IO ()
main =
  do
    pargs ← getArgs
    case pargs of
      [] → repl
      _ → void $ mapM processFile pargs
      
