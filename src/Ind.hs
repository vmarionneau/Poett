{-# LANGUAGE UnicodeSyntax #-}

module Ind (module Ind) where

data Lvl = Type Int | Prop
  deriving (Eq, Show)

data Arity ty = Arity
  { arArgs :: [ty],
    arSort :: Lvl
  }
  deriving (Eq, Show)

data CsArg ty = CsArg
  {
    argArgs :: [ty],
    argRes :: ty,
    argRec :: Bool
  }
  deriving (Eq, Show)

data Constructor ty = Constructor
  { csName :: String,
    csArgs :: [CsArg ty],
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

csArgsLength :: Constructor ty → Int
csArgsLength cs = length (csArgs cs)

indParamLength :: Ind ty → Int
indParamLength ind = length (indParams ind)

indIndicesLength :: Ind ty → Int
indIndicesLength ind = length (arArgs $ indArity ind)

indArgLength :: Ind ty → Int
indArgLength ind = indParamLength ind + indIndicesLength ind

elimArgLength :: Ind ty → Int
elimArgLength ind = indParamLength ind + 1 + length (indConstructors ind) + indIndicesLength ind + 1
{-
  Parameters
  Type family
  Patterns
  Indices
  Constructor
-}
csFullArgsLength :: Ind ty → Int → Int
csFullArgsLength ind i = indArgLength ind + csArgsLength (indConstructors ind !! i)

