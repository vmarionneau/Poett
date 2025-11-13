{-# LANGUAGE UnicodeSyntax #-}

module Ind (module Ind) where
import Name
import Term

data Arity ty = Arity
  { arArgs :: [(Name, ty)],
    arSort :: Lvl
  }
  deriving (Eq, Show)

data CsArg ty = CsArg
  {
    argArgs :: [(Name, ty)],
    argRes :: ty,
    argRec :: Bool
  }
  deriving (Eq, Show)

data Constructor ty = Constructor
  { csName :: String,
    csArgs :: [(Name, CsArg ty)],
    csResIndices :: [ty]
  }
  deriving (Eq, Show)

data Ind ty = Ind
  { indName :: String,
    indParams :: [(Name, ty)],
    indArity :: Arity ty,
    indConstructors :: [Constructor ty]
  }
  deriving (Eq, Show)

indIndices :: Ind ty → [(Name, ty)]
indIndices = arArgs . indArity

csArgsLength :: Constructor ty → Int
csArgsLength = length . csArgs

indParamLength :: Ind ty → Int
indParamLength = length . indParams 

indIndicesLength :: Ind ty → Int
indIndicesLength = length . indIndices

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

