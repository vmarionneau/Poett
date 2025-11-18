{-# LANGUAGE UnicodeSyntax #-}

module Syntax (module Syntax) where

import Name
import Term
import Ind
import Ctx
import WHNF
import Typecheck
import qualified Control.Monad.Reader as R
import Control.Monad (void)
import Data.Maybe (fromMaybe)
import Data.List (elemIndex)

-- Pre Terms
data PTm
  = PBVar Int
  | PU Lvl
  | PPi String PTy PTy
  | PAbs String PTy PTm
  | PApp PTm [PTm]
  | PLet String PTy PTm PTm
  | PElim Lvl String
  | PIdent String
  | PCast PTm PTy
  deriving (Eq, Show)

type PTy = PTm

data PreInd = PreInd
  {
    preIndName :: String,
    preIndParams :: [(String, PTy)],
    preIndArity :: PTy,
    preIndConstructors :: [(String, PTy)]
  }
  deriving (Eq, Show)

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

toBound :: PTm → R.Reader [String] PTm
toBound (PIdent s) =
  do
    names ← R.ask
    pure <$> fromMaybe (PIdent s) $ PBVar <$> s `elemIndex` names
toBound (PPi s ty fam) =
  do
    names ← R.ask
    ty' ← toBound ty
    fam' ← R.local (s:) (toBound fam)
    pure $ PPi s ty' fam'
toBound (PAbs s ty tm) =
  do
    names ← R.ask
    ty' ← toBound ty
    tm' ← R.local (s:) (toBound tm)
    pure $ PAbs s ty' tm'
toBound (PApp tm args) =
  do
    tm' ← toBound tm
    args' ← mapM toBound args
    pure $ PApp tm' args'
toBound (PLet s ty tm body) =
  do
    names ← R.ask
    ty' ← toBound ty
    tm' ← toBound tm
    body' ← R.local (s:) (toBound body)
    pure $ PLet s ty' tm' body'
toBound (PCast tm ty) =
  do
    tm' ← toBound tm
    ty' ← toBound ty
    pure $ PCast tm' ty'
toBound tm = pure tm

boundToTerm :: PTm → InCtx Tm
boundToTerm (PIdent s) =
  do
    bDef ← isDef s
    bInd ← isInd s
    if bDef || bInd
      then pure $ Ident s
      else
      do
        (nameInd, i) ← asConstr s
        pure $ Constr nameInd i
boundToTerm (PU lvl) = pure $ U lvl
boundToTerm (PPi name ty fam) =
  do
    ty' ← boundToTerm ty
    fam' ← boundToTerm fam
    pure $ Pi (named name) ty' fam'
    
boundToTerm (PAbs name ty tm) =
  do
    ty' ← boundToTerm ty
    tm' ← boundToTerm tm
    pure $ Abs (named name) ty' tm'
boundToTerm (PApp tm args) =
  do
    tm' ← boundToTerm tm
    args' ← mapM boundToTerm args
    pure $ App tm' args'
boundToTerm (PLet name ty tm body) =
  do
    ty' ← boundToTerm ty
    tm' ← boundToTerm tm
    body' ← boundToTerm body
    pure $ Let (named name) ty' tm' body'
boundToTerm (PCast tm ty) =
  do
    tm' ← boundToTerm tm
    ty' ← boundToTerm ty
    pure $ Cast tm' ty'
boundToTerm (PBVar i) = pure $ BVar i
boundToTerm (PElim lvl ind) =
  do
    void $ getInd ind
    pure $ Elim lvl ind

toTerm :: PTm → InCtx Tm
toTerm tm =
    let bound = R.runReader (toBound tm) []
    in boundToTerm bound
    
-- TODO : Convert PreInd to Ind
