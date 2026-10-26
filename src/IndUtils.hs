{-# LANGUAGE UnicodeSyntax #-}

module IndUtils (module IndUtils) where

import Name
import Term
import Ind
import Ctx
import Control.Monad (void)

arToType :: [Name] → Arity Ty → InCtx Ty
arToType paramNames ar =
  do
    let args = arArgs ar
    argNames ← addTelescope $ instantiateTele (FVar <$> paramNames) args
    closeProducts argNames $ U (arSort ar)

indType :: Ind Ty → InCtx Ty
indType ind =
  do
    let params = indParams ind
    paramNames ← addTelescope params
    arType ← arToType paramNames (indArity ind)
    closeProducts paramNames arType
 
csArgType :: [Name] → [Name] → CsArg Ty → InCtx Ty
csArgType paramNames csArgNames arg =
  do
    let args = instantiateTele (FVar <$> (csArgNames ++ paramNames)) $ argArgs arg
    argNames ← addTelescope args
    let resArgTy = instantiate (FVar <$> (argNames ++ csArgNames ++ paramNames)) (argRes arg)
    closeProducts argNames resArgTy

constrType' :: [Name] → Ind Ty → Int → InCtx Ty
constrType' paramNames ind i =
  do
    cst ← getConstr ind i
    let args = csArgs cst
    argNames ← aux args []
    closeProducts argNames
      $ App (Ident (indName ind))
      $ (FVar <$> reverse paramNames)
      ++ (instantiate (FVar <$> (argNames ++ paramNames)) <$> csResIndices cst)
      where
        aux :: [(Name, CsArg Ty)] → [Name] → InCtx [Name]
        aux [] csArgNames = pure csArgNames
        aux ((argName, arg):args) csArgNames =
          do
            argType ← csArgType paramNames csArgNames arg
            argName' ← addVar argName argType
            aux args (argName':csArgNames)

constrType :: Ind Ty → Int → InCtx Ty
constrType ind i =
  do
    let params = indParams ind
    paramNames ← addTelescope params
    ty ← constrType' paramNames ind i
    closeProducts paramNames ty

-- The following are not yet used anywhere

hasSealedElim :: Tm → InCtx Bool
hasSealedElim (Pi _ ty fam) = 
    do
      b1 ← hasSealedElim ty
      b2 ← hasSealedElim fam
      pure $ b1 || b2
hasSealedElim (Abs _ ty bod) = 
    do
      b1 ← hasSealedElim ty
      b2 ← hasSealedElim bod
      pure $ b1 || b2
hasSealedElim (App tm args) = 
    do
      b ← hasSealedElim tm
      bs ← mapM hasSealedElim args
      pure $ b || any id bs
hasSealedElim (Let _ ty tm bod) = 
    do
      b1 ← hasSealedElim ty
      b2 ← hasSealedElim tm
      b3 ← hasSealedElim bod
      pure $ b1 || b2 || b3
hasSealedElim (Cast tm ty) = 
    do
      b1 ← hasSealedElim tm
      b2 ← hasSealedElim ty
      pure $ b1 && b2
hasSealedElim (Elim _ name) =
    do 
      ind ← getInd name
      pure $ isIndSealed ind
hasSealedElim _ = pure False

ensureNoSealedElim :: Tm → InCtx ()
ensureNoSealedElim (Pi _ ty fam) = 
    do
      ensureNoSealedElim ty
      ensureNoSealedElim fam
ensureNoSealedElim (Abs _ ty bod) = 
    do
      ensureNoSealedElim ty
      ensureNoSealedElim bod
ensureNoSealedElim (App tm args) = 
    do
      ensureNoSealedElim tm
      void $ mapM ensureNoSealedElim args
ensureNoSealedElim (Let _ ty tm bod) = 
    do
      ensureNoSealedElim ty
      ensureNoSealedElim tm
      ensureNoSealedElim bod
ensureNoSealedElim (Cast tm ty) = 
    do
      ensureNoSealedElim tm
      ensureNoSealedElim ty
ensureNoSealedElim (Elim _ name) =
    do 
      ind ← getInd name
      if isIndSealed ind
      then fail $ "Can't eliminate on sealed inductive type " ++ name
      else pure ()
ensureNoSealedElim _ = pure ()
