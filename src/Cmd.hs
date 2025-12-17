{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Cmd (module Cmd) where

import Syntax
import Term
import Ctx
import Syntax
import Parser
import WHNF
import Typecheck
import Elab
import Data.Maybe (fromMaybe)
import System.IO (isEOF)
import Control.Monad (void, foldM)

processDef :: DefCmd → InCtx (IO ())
processDef df =
  case defCmdType df of
    Just pty →
      do
        ty ← toTerm pty
        ensureType ty
        tm ← toTerm (defCmdBody df)
        check tm ty
        addDef (defCmdName df) tm ty
        pure $ pure ()
    Nothing →
      do
        tm ← toTerm (defCmdBody df)
        ty ← infer tm
        addDef (defCmdName df) tm ty
        pure $ pure ()

processAx :: String → PTy → InCtx (IO ())
processAx name pty =
  do
    ty ← toTerm pty
    ensureType ty
    addCst name ty
    pure $ pure ()

processInd :: PreInd → InCtx (IO ())
processInd pind =
  do
    ind ← toInd pind
    addInd ind
    pure $ pure ()

processCheck :: PTm → InCtx (IO ())
processCheck ptm =
  do
    tm ← toTerm ptm
    sTm ← showTermCtx tm
    ty ← infer tm
    sTy ← showTermCtx ty
    pure $ putStrLn (sTm ++ " : " ++ sTy)

processPrint :: String → InCtx (IO ())
processPrint name =
  do
    bdef ← isDef name
    bInd ← isInd name
    if bdef then
      do
        { df ← getDef name
        ; let body = fromMaybe (Ident name) (defBody df)
        ; let ty = defType df
        ; sTm ← showTermCtx body
        ; sTy ← showTermCtx ty
        ; pure $ putStrLn (sTm ++ " : " ++ sTy)
        }
      else if bInd then
       do
         { ind ← getInd name
         ; pure $ print ind
         }
      else fail $ "Not a defined constant : " ++ name

processFail :: Command → Ctx → IO (Either String Ctx)
processFail cmd ctx =
  do
    x ← processCommand cmd ctx
    case x of
      Right _ → pure $ Left "Command has not failed !"
      Left err → (putStrLn $ "Command has indeed failed with message : " ++ err) >> (pure $ Right ctx)

processNF :: PTm → InCtx (IO ())
processNF ptm =
  do
    tm ← toTerm ptm
    _ ← infer tm
    tm' ← nf tm
    sTm ← showTermCtx tm'
    pure $ putStrLn sTm

processHNF :: PTm → InCtx (IO ())
processHNF ptm =
  do
    tm ← toTerm ptm
    _ ← infer tm
    tm' ← hnf tm
    sTm ← showTermCtx tm'
    pure $ putStrLn sTm

processWHNF :: PTm → InCtx (IO ())
processWHNF ptm =
  do
    tm ← toTerm ptm
    _ ← infer tm
    tm' ← whnf tm
    sTm ← showTermCtx tm'
    pure $ putStrLn sTm

unpackForIO :: InCtx (IO ()) → Ctx → IO (Either String Ctx)
unpackForIO mx ctx =
  do
    let x = runInCtx mx ctx
    case x of
      Left err → pure $ Left err
      Right (ctx', my) → my >> (pure $ Right ctx')

processCommand :: Command → Ctx → IO (Either String Ctx)
processCommand (Definition df) = unpackForIO $ processDef df
processCommand (Inductive pind) = unpackForIO $ processInd pind
processCommand (Axiom name pty) = unpackForIO $ processAx name pty
processCommand (Check ptm) = unpackForIO $ processCheck ptm
processCommand (Print name) = unpackForIO $ processPrint name
processCommand (Import path) = processFile (path ++ ".poett")
processCommand (Fail cmd) = processFail cmd
processCommand (NF ptm) = unpackForIO $ processNF ptm
processCommand (HNF ptm) = unpackForIO $ processHNF ptm
processCommand (WHNF ptm) = unpackForIO $ processWHNF ptm

processInput :: String → Ctx → IO (Either String Ctx)
processInput input ctx =
  do
    let inctx =
          do
            { (toks, rest) ← inCtxOfMaybe "Lexing failed" $ runParser lexer $ Stream input 0 0
            ; (cmds, rest') ← inCtxOfMaybe "Parsing failed" $ runParser script $ Scoped toks []
            ; if (streamData rest) /= []
              then fail $ "Lexer error at : " ++ show (streamRow rest, streamCol rest) ++ " : " ++ show (streamData rest)
              else
                case (scopedData rest') of
                  h:_ → fail $ "Parser error at : " ++ show (pos h)
                  [] → pure $ processCommand <$> locData <$> cmds
            }
    case runInCtx inctx ctx of
      Left msg → pure $ Left msg
      Right (ctx', actions) →
        foldM (\ mctx action →
                  case mctx of
                    Left err → pure $ Left err
                    Right ctx'' → action ctx''
              ) (Right ctx') actions

processFile :: String → Ctx → IO (Either String Ctx)
processFile fileName ctx =
  do
    file ← readFile fileName
    ctx' ← processInput file ctx
    case ctx' of
      Left err →
        let err' = "Import of file '" ++ fileName ++ "' has failed with error : " ++ err
        in do
          { putStrLn err'
          ; pure $ Left err'
          } 
      Right ctx'' → pure $ Right ctx''

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
                do mctx ← processInput (unlines ls) ctx
                   case mctx of
                     Left err → putStrLn err >> aux [] ctx
                     Right ctx' → aux [] ctx'
              else aux (ls ++ [l]) ctx
            }
