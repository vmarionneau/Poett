{-# LANGUAGE UnicodeSyntax #-}

module Ind (module Ind) where

data Lvl = Type Int | Prop
  deriving (Eq, Show)

data Arity ty = Arity
  { arArgs :: [ty],
    arSort :: Lvl
  }
  deriving (Eq, Show)

data Constructor ty = Constructor
  { csName :: String,
    csArgs :: [ty],
    csResult :: ty
  }
  deriving (Eq, Show)

data Ind ty = Ind
  { indName :: String,
    indParams :: [ty],
    indArity :: Arity ty,
    indConstructors :: [Constructor ty]
  }
  deriving (Eq, Show)

indArgLength :: Ind ty → Int
indArgLength ind = length (indParams ind) + length (arArgs $ indArity ind)

elimArgLength :: Ind ty → Int
elimArgLength ind = indArgLength ind + length (indConstructors ind) + 1 
