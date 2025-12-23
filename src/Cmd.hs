{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Cmd (module Cmd) where

import Syntax
import Term
import Ctx
import Parser
import WHNF
import Typecheck
import Elab
import Data.Maybe (fromMaybe)
import System.IO (isEOF)
import System.Directory (getCurrentDirectory)
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

processProof :: DefCmd → InCtx (IO ())
processProof pf =
  case defCmdType pf of
    Just pty →
      do
        ty ← toTerm pty
        ensureType ty
        tm ← toTerm (defCmdBody pf)
        check tm ty
        addCst (defCmdName pf) ty
        pure $ pure ()
    Nothing →
      do
        tm ← toTerm (defCmdBody pf)
        ty ← infer tm
        addCst (defCmdName pf) ty
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

processFail :: Command → FilePath → Ctx → IO (Either String Ctx)
processFail cmd path ctx =
  do
    x ← processCommand cmd path ctx
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

unpackForIO :: InCtx (IO ()) → FilePath → Ctx → IO (Either String Ctx)
unpackForIO mx _ ctx =
  do
    let x = runInCtx mx ctx
    case x of
      Left err → pure $ Left err
      Right (ctx', my) → my >> (pure $ Right ctx')

processCommand :: Command → FilePath → Ctx → IO (Either String Ctx)
processCommand (Definition df) = unpackForIO $ processDef df
processCommand (Proof pf) = unpackForIO $ processProof pf
processCommand (Inductive pind) = unpackForIO $ processInd pind
processCommand (Axiom name pty) = unpackForIO $ processAx name pty
processCommand (Check ptm) = unpackForIO $ processCheck ptm
processCommand (Print name) = unpackForIO $ processPrint name
processCommand (Import path) = processImport (path ++ ".poett")
processCommand (Fail cmd) = processFail cmd
processCommand (NF ptm) = unpackForIO $ processNF ptm
processCommand (HNF ptm) = unpackForIO $ processHNF ptm
processCommand (WHNF ptm) = unpackForIO $ processWHNF ptm

processInput :: String → FilePath → Ctx → IO (Either String Ctx)
processInput input path ctx =
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
                  [] → pure $ (flip processCommand path)  <$> locData <$> cmds
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
    let path = split '/' fileName
    let pathUp = take (length path - 1) path
    let root = (intercalate "/" pathUp) ++ "/"
    ctx' ← processInput file root ctx
    case ctx' of
      Left err →
        let err' = "Import of file '" ++ fileName ++ "' has failed with error : " ++ err
        in do
          { putStrLn err'
          ; pure $ Left err'
          } 
      Right ctx'' → pure $ Right ctx''

split :: Char → String → [String]
split _ [] = []
split x (c:cs) =
  if c == x
  then
    "":split x cs
  else 
    case split x cs of
      [] → [[c]]
      h:t → (c:h):t

processImport :: String → FilePath → Ctx → IO (Either String Ctx)
processImport fileName root ctx = processFile (root ++ fileName) ctx

repl :: IO ()
repl =
  do
    path ← getCurrentDirectory
    aux (path ++ "/") [] emptyCtx
      where
        aux path ls ctx =
          do
            end ← isEOF
            if end
              then void $ processInput (unlines ls) path ctx 
              else
              do
                { l ← getLine
                ; if l == []
                  then
                    do mctx ← processInput (unlines ls) path ctx
                       case mctx of
                         Left err → putStrLn err >> aux path [] ctx
                         Right ctx' → aux path [] ctx'
                  else aux path (ls ++ [l]) ctx
                }
