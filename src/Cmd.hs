{-# LANGUAGE UnicodeSyntax #-}

module Cmd (module Cmd) where

import Syntax
import Term
import Ctx
import WHNF
import Typecheck
import Elab
import Data.Maybe (fromMaybe)

data DefCmd = DefCmd { defCmdName :: String, defCmdType :: Maybe PTy, defCmdBody :: PTm }
  deriving (Eq, Show)

data Command
  = Definition DefCmd
  | Inductive PreInd
  | Check PTm
  | Print String
  | Fail Command
  | NF PTm
  | HNF PTm
  | WHNF PTm
  deriving (Eq, Show)

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
    ty ← infer tm
    sTy ← showTermCtx ty
    pure $ putStrLn sTy

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

processFail :: Command → InCtx (IO ())
processFail cmd =
  isolate $
  do
    x ← inCtxTry $ processCommand cmd
    case x of
      Right _ → fail "Command has not failed !"
      Left err → pure $ putStrLn $ "Command has indeed failed with message : " ++ err

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

processCommand :: Command → InCtx (IO ())
processCommand (Definition df) = processDef df
processCommand (Inductive pind) = processInd pind
processCommand (Check ptm) = processCheck ptm
processCommand (Print name) = processPrint name
processCommand (Fail cmd) = processFail cmd
processCommand (NF ptm) = processNF ptm
processCommand (HNF ptm) = processHNF ptm
processCommand (WHNF ptm) = processWHNF ptm
