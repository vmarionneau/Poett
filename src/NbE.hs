{-# LANGUAGE UnicodeSyntax #-}

module NbE (module NbE) where

import Control.Monad.Except (throwError)
import Data.List ((!?))
import qualified Term as T (Tm (..))
import qualified Ind as I (Lvl, Arity, Constructor, Ind)

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither a Nothing = Left a
maybeToEither _ (Just b) = Right b

type Env = [Value]

data Value
  = U I.Lvl
  | Pi Value Closure
  | Abs Closure
  | Constr (I.Ind Value) Int [Value]
  | Neutral Neutral
  deriving (Eq, Show)

data Neutral
  = Var Int
  | App Neutral Value
  | Elim (I.Ind Value) [Value] Neutral
  deriving (Eq, Show)

data Closure = Closure {cTerm :: T.Tm, cEnv :: Env}
  deriving (Eq, Show)

eval :: Env -> T.Tm -> Either String Value
eval γ (T.Var i) =
  maybeToEither "Unbound variable" (γ !? i)
eval _ (T.U lvl) = pure $ U lvl
eval γ (T.Pi base fam) =
  do
    vbase <- eval γ base
    let cfam = Closure fam γ
    pure $ Pi vbase cfam
eval γ (T.Abs _ body) =
  pure $ Abs (Closure body γ)
eval γ (T.App fn arg) =
  do
    vfn <- eval γ fn
    varg <- eval γ arg
    case vfn of
      Abs (Closure body γ') -> eval (varg : γ') body
      Neutral ne -> pure $ Neutral (App ne varg)
      _ -> throwError "Expected function got something else"
eval γ (T.Let term body) =
  do
    vterm <- eval γ term
    eval (vterm : γ) body
eval _ (T.Ident {}) = throwError "Unimplemented : Identifiers"
eval _ (T.Constr {}) = throwError "Unimplemented : Constructors"
eval _ (T.Elim {}) = throwError "Unimplemented : Eliminators"
