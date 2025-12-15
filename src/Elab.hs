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
    aux :: [Name] → [(String, PTy)] → InCtx [Name]
    aux params [] = pure params
    aux params ((name, pty):ps) =
      do
        ty ← toTerm pty
        let ty' = instantiate (FVar <$> params) ty
        ensureType ty'
        pName ← addVar (named name) ty'
        aux (pName:params) ps
        
toArity :: [Name] → PTy → InCtx (Arity Ty)
toArity pNames pty =
  do
    ty ← toTerm pty
    ty' ← nf (instantiate (FVar <$> pNames) ty)
    ensureType ty'
    let (args, body) = unravelPi (-1) ty'
    case body of
      U lvl → pure $ Arity args lvl
      _ → fail "Not an arity"

abstractArity :: [Name] → Arity Ty → InCtx (Arity Ty)
abstractArity pNames ar =
  do
    let args = arArgs ar
    argNames ← addTelescope $ args
    ty ← closeProducts argNames $ U (arSort ar)
    let ty' = abstract pNames ty
    case unravelPi (-1) ty' of
      (args, U lvl) → pure $ Arity args lvl
      _ → fail "Unreachable error has been reached"

-- Note : This should be run on the output of toArity and not on the one of abstractArity
foldArity :: [Name] → Arity Ty → InCtx Ty
foldArity pNames ar =
  isolate $
    do
      let args = arArgs ar
      argNames ← addTelescope $ args
      closeProducts (argNames ++ pNames) $ U (arSort ar)

toCsArgs :: String → [Name] → [(Name, Ty)] → InCtx [(Name, CsArg Ty)]
toCsArgs nameInd pNames args =
  do
    args' ← aux args []
    let (argNames, recs) = unzip args'
    ty ← closeProducts argNames $ Ident "Dummy"
    let ty' = abstract pNames ty
    let (args'', _) = unravelPi (-1) ty
    pure $ zipWith (\ (name, ty) isRec → let (args, body) = unravelPi (-1) ty in (name, CsArg args body isRec)) args'' (reverse recs)
  where
    aux :: [(Name,Ty)] → [(Name, Bool)] → InCtx [(Name, Bool)]
    aux [] names = pure names
    aux ((name,ty):args) names =
      do
        let ty' = instantiate ((FVar . fst) <$> names) ty
        ensureType ty'
        nfTy ← nf ty'
        isRec ← checkRec ty'
        name' ← addVar name ty'
        aux args ((name', isRec):names)

    checkRec (Pi _ ty fam) =
      do
        checkAbsence ty
        checkRec fam
    checkRec (App func args) =
      do
        mapM checkAbsence args
        let pars = take (length pNames) args
        if func == Ident nameInd then
          if pars /= (FVar <$> (reverse pNames)) then
            fail $ "Parameters should be constant inside types of constructors for " ++ nameInd
          else pure True
          else 
          checkAbsence func >> pure False
    -- No need to check for the number of arguments, it typechecks
    checkRec (Ident s) = pure $ s /= nameInd
    checkRec (Cast tm ty) =
      do
        checkAbsence ty
        checkRec tm
    checkRec tm = checkAbsence tm >> pure False

    checkAbsence (Ident s) =
      if s == nameInd
      then fail $ "Non stricttly positive occurence of " ++ nameInd ++ " found"
      else pure ()
    checkAbsence (Pi _ ty fam) = checkAbsence ty >> checkAbsence fam
    checkAbsence (Abs _ ty tm) = checkAbsence ty >> checkAbsence tm
    checkAbsence (App tm args) = checkAbsence tm >> mapM checkAbsence args >> pure ()
    checkAbsence (Let _ ty tm body) = checkAbsence ty >> checkAbsence tm >> checkAbsence body
    checkAbsence (Cast tm ty) = checkAbsence tm >> checkAbsence ty
    checkAbsence _ = pure ()
        
toConstructor :: String → [Name] → (String, PTy) → InCtx (Constructor Ty)
toConstructor nameInd pNames (name, pty) =
  do
    ty ← toTerm pty
    ty' ← nf (instantiate (FVar <$> pNames) ty)
    ensureType ty'
    let (args, body) = unravelPi (-1) ty'
    cArgs ← toCsArgs name pNames args
    let (tm, tmArgs) = asApp body
    let pars = take (length pNames) tmArgs
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
      else
        let ty'' = abstract pNames ty' in
        let (_, body') = unravelPi (-1) ty'' in
        let (_, tmArgs') = asApp body' in
        let indices = drop (length pNames) tmArgs' in
          pure $ Constructor name cArgs indices
             

toInd :: PreInd → InCtx (Ind Ty)
toInd pind =
  do
    let name = preIndName pind
    pNames ← toParams (preIndParams pind)
    -- Must do a first pass to convert identifiers referring to
    -- parameters into their proper bound variables
    arity ← toArity pNames $ preIndArity pind
    ar ← abstractArity pNames arity
    cstTy ← foldArity pNames arity
    addCst name cstTy
    csts ← mapM (toConstructor name pNames) $ preIndConstructors pind
    removeDef name
    ty ← closeProducts pNames (Ident "dummy")
    let (params', _) = unravelPi (-1) ty
    pure $ Ind name params' arity csts
