{-# LANGUAGE UnicodeSyntax #-}

{- According to : https://inria.hal.science/hal-01094195v1 -}

module Term (module Term) where

{-
import Data.Set (Set)
import qualified Data.Set as Set
import Ind
data Tm
  = Var Int
  | U Lvl
  | Pi Ty Ty
  | Abs Ty Tm
  | App Tm Tm
  | Let Tm Tm
  | Ident String
  | Constr (Ind Ty) Int
  | Elim (Ind Ty)
  deriving (Eq, Show)

type Ty = Tm

vars :: Tm -> Set Int
vars (Var i) = Set.singleton i
vars (Pi t1 t2) = vars t1 `Set.union` Set.map (flip (-) 1) (Set.delete 0 (vars t2))
vars (Abs t1 t2) = vars t1 `Set.union` Set.map (flip (-) 1) (Set.delete 0 (vars t2))
vars (App t1 t2) = vars t1 `Set.union` vars t2
vars _ = Set.empty
-}
