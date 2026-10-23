{-# LANGUAGE UnicodeSyntax #-}

module IndUtils (module IndUtils) where

import Name
import Term
import Ind
import Ctx

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
