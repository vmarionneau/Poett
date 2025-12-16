{-# LANGUAGE UnicodeSyntax #-}

module Cmd (module Cmd) where

import Name
import Syntax
import Term
import Ind
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
    pure $ (print ty)

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
        ; pure $ putStrLn (show body ++ " : " ++ show ty)
        }
      else if bInd then
       do
         { ind ← getInd name
         ; pure $ print ind
         }
      else fail $ "Not a defined constant : " ++ name

processNF :: PTm → InCtx (IO ())
processNF ptm =
  do
    tm ← toTerm ptm
    _ ← infer tm
    tm' ← nf tm
    pure $ print tm'

processHNF :: PTm → InCtx (IO ())
processHNF ptm =
  do
    tm ← toTerm ptm
    _ ← infer tm
    tm' ← hnf tm
    pure $ print tm'

processWHNF :: PTm → InCtx (IO ())
processWHNF ptm =
  do
    tm ← toTerm ptm
    _ ← infer tm
    tm' ← whnf tm
    pure $ print tm'

processCommand :: Command → InCtx (IO ())
processCommand (Definition df) = processDef df
processCommand (Inductive pind) = processInd pind
processCommand (Check ptm) = processCheck ptm
processCommand (Print name) = processPrint name
processCommand (NF ptm) = processNF ptm
processCommand (HNF ptm) = processHNF ptm
processCommand (WHNF ptm) = processWHNF ptm
