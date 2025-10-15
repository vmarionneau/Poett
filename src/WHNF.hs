{-# LANGUAGE UnicodeSyntax #-}

module WHNF (module WHNF) where

import qualified Term as T (Tm, Ty)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Ind

data Subst = Subst { vars :: [STm], idents :: Map.Map String STm }
  deriving (Eq, Show)

data STm
  = Var Int
  | U Lvl
  | Pi STy STy
  | Abs STy STm
  | App STm [STm]
  | Let STm STm
  | Ident String
  | Constr (Ind STy) Int
  | Elim (Ind STy)
  | ESubst Subst STm
  deriving (Eq, Show)

type STy = STm

lift :: Subst → Subst
lift s = Subst (Var 0 : vars s) (idents s)

concatSubst :: Subst → Subst → Subst
concatSubst s1 s2 = Subst (vars s1 ++ vars s2) (idents s1 `Map.union` idents s2)

pushSubst :: STm → STm
pushSubst (ESubst sb t) = aux sb t
  where
    aux s (ESubst s' t') = aux (concatSubst s s') t'
    aux s (Var i) = vars s !! i
    aux _ (U l) = U l
    aux s (Pi ty tm) = Pi (ESubst (lift s) ty) (ESubst s tm)
    aux s (Abs ty tm) = Abs (ESubst (lift s) ty) (ESubst s tm)
    aux s (App tm1 args) = App (ESubst s tm1) ((\ x -> ESubst s x) <$> args)
    aux s (Let tm1 tm2) = Let (ESubst s tm1) (ESubst (lift s) tm2)
    aux s (Ident i) = fromMaybe (Ident i) (idents s Map.!? i)
    aux _ (Constr ind i) = Constr ind i
    aux _ (Elim ind) = Elim ind
pushSubst t = t 

whnf :: STm → STm
whnf s@(ESubst _ _) = whnf (pushSubst s)
whnf (App l []) = whnf l
whnf (App l r) = 
  case whnf l of
    Abs _ tm -> whnf (ESubst (Subst (reverse r) Map.empty) tm)
    App l' r' -> whnf (App l' (r' ++ r)) 
    Elim ind -> let len = elimArgLength ind in
                  if length r >= len
                  then
                    let args = take (len - 1) r in
                    let cst = whnf (r !! len) in
                    let rest = drop len r in
                      case cst of
                        Constr _ i ->
                          let pat = args !! (indArgLength ind + i) in
                            whnf (App pat rest)
                        cst' -> App (Elim ind) (args ++ cst':rest)
                  else App (Elim ind) r
                   
    l' -> App l' r
whnf (Let tm1 tm2) = whnf (ESubst (Subst [tm2] Map.empty) tm1)
whnf t = t

