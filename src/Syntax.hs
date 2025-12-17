{-# LANGUAGE UnicodeSyntax #-}

module Syntax (module Syntax) where
import Term

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
  | Axiom String PTy
  | Check PTm
  | Print String
  | Import String
  | Fail Command
  | NF PTm
  | HNF PTm
  | WHNF PTm
  deriving (Eq, Show)
