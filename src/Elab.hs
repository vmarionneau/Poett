{-# LANGUAGE UnicodeSyntax #-}

module Elab (module Elab) where

import Name
import Syntax
import Term
import Ind
import Ctx
import Elim
import WHNF
import Typecheck
import qualified Control.Monad.Reader as R
import Control.Monad (void)
import Data.Maybe (fromMaybe)
import Data.List (elemIndex)

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

toParams :: [(String, PTy)] → InCtx [Name]
toParams = aux []
  where
    aux params [] = pure params
    aux params ((name, pty):ps) =
      do
        ty ← toTerm pty
        ty' ← instantiate params ty
        ensureType ty'
        pName ← addVar (named name) ty'
        aux (pName:params) ps
        
toArity :: [Name] → PTy → InCtx (Arity Ty)
toArity pNames pty =
  do
    ty ← toTerm pty
    ty' ← nf (instantiate (FVar <$> pNames) ty)
    ensureType ty'
    (args, body) ← unravelPi ty'
    case body of
      U lvl → pure $ Arity args lvl
      _ → fail "Not an arity"

-- TODO 
toCsArgs :: String → [(Name, Ty)] → InCtx ([CsArg Ty])
toCsArgs _ _ = fail "Not Yet Implemented"

toConstructor :: String → [Name] → (String, PTy) → InCtx (Constructor Ty)
toConstructor nameInd pNames (name, pty) =
  do
    ty ← toTerm pty
    ty' ← nf (instantiate (FVar <$> pNames) ty)
    (args, body) ← unravelPi ty'
    cArgs ← toCsArgs name args
    let (tm, tmArgs) = asApp body
    let pars = take (length pNames) tmArgs
    let indices = drop (length pNames) tmArgs
    if tm /= Ident nameInd
      then fail
           $ "Type of constructor "
           ++ name
           ++ " should end in an application of inductive type "
           ++ nameInd
      else if pars /= (FVar <$> (reverse pNames))
      then fail
           $ "Return type of constructor "
           ++ name
           ++ " should is not applied to the correct parameters"
      else pure $ Constructor name cArgs indices

toInd :: PreInd → InCtx (Ind Ty)
toInd pind =
  do
    let name = preIndName pind
    pNames ← toParams (preIndParams pind) []
    arity ← toArity pNames $ preIndArity pind
    csts ← mapM (toConstructor name pNames) $ preIndConstructors pind
    -- /!\ Abstract over the parameter names /!\
    pure $ Ind name params' arity csts
  
