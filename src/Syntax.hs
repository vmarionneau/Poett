{-# LANGUAGE UnicodeSyntax #-}

module Syntax (module Syntax) where
import Term
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
