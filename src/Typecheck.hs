{-# LANGUAGE UnicodeSyntax #-}

module Typecheck (module Typecheck) where

import Name
import Ind
import Term
import Ctx
import Elim
import WHNF
import Data.Maybe (fromMaybe)
import Control.Monad (foldM)
import qualified Data.Map as Map

piLvl :: Lvl → Lvl → Lvl
piLvl _ Prop = Prop
piLvl Prop (Type i) = Type i
piLvl (Type i) (Type j) = Type (i `max` j)

asU :: Tm → InCtx Lvl
asU (U lvl) = pure lvl
asU ty =
  do
    sTy ← showTermCtx ty
    fail $ "Expected universe got " ++ sTy

asPi :: Ty → InCtx (Name, Ty, Ty)
asPi (Pi name ty fam) = pure (name, ty, fam)
asPi ty =
  do
    sTy ← showTermCtx ty
    fail $ "Expected product got " ++ sTy

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
    
constrType :: Ind Ty → Int → InCtx Ty
constrType ind i =
  do
    cst ← getConstr ind i
    let params = indParams ind
    paramNames ← addTelescope params
    let args = csArgs cst
    argNames ← aux paramNames (csArgs cst) []
    closeProducts (argNames ++ paramNames)
      $ App (Ident (indName ind))
      $ (FVar <$> reverse paramNames)
      ++ (instantiate (FVar <$> (argNames ++ paramNames)) <$> csResIndices cst)
      where
        aux :: [Name] → [(Name, CsArg Ty)] → [Name] → InCtx [Name]
        aux _ [] csArgNames = pure csArgNames
        aux paramNames ((argName, arg):args) csArgNames =
          do
            argType ← csArgType ind paramNames csArgNames arg
            argName' ← addVar argName argType
            aux paramNames args (argName':csArgNames)
            
infer :: Tm → InCtx Ty
infer (FVar name) =
  do
    entry ← getLocal name
    pure $ entryType entry
infer (U Prop) = pure $ U (Type 0)
infer (U (Type i)) = pure $ U (Type (i + 1))
infer (Pi name ty fam) =
  do
    u ← infer ty
    lvl ← whnf u >>= asU
    var ← addVar name ty
    u' ← infer $ instantiate [FVar var] fam
    lvl' ← whnf u' >>= asU
    removeDecl var
    pure $ U (piLvl lvl lvl')
infer (Let name ty tm1 tm2) =
  do
    check tm1 ty
    letVar ← addLocal name ty tm1
    ty ← infer $ instantiate [FVar letVar] tm2
    unfoldLocal letVar ty
infer (Ident s) =
  do
    bdef ← isDef s
    if bdef
      then defType <$> getDef s
      else getInd s >>= indType
infer (Abs name ty tm) =
  do
    u ← infer ty
    whnf u >>= asU
    var ← addVar name ty
    tyRes ← infer $ instantiate [FVar var] tm
    removeDecl var
    pure $ Pi var ty (abstract [var] tyRes)
infer (App tm args) =
  do
    ty ← infer tm
    foldM (\ aty arg →
              do
                (name, tyarg, tyres) ← whnf aty >>= asPi
                check arg tyarg
                pure $ instantiate [arg] tyres
          ) ty args
infer (Cast tm ty) = check tm ty >> pure ty
infer (Constr nameInd i) =
  do
    ind ← getInd nameInd
    constrType ind i
infer (Elim lvl nameInd) =
  do
    ind ← getInd nameInd
    checkElim ind lvl
    elimType ind lvl
infer (BVar _) = fail "Can't infer type of bound variables, convert them to free variables first"
    
check :: Tm → Ty → InCtx ()
check tm ty =
  do
    u ← infer ty
    whnf u >>= asU
    tyinf ← infer  tm
    b ← conv ty tyinf
    if b
      then pure ()
      else do
      sTm ← showTermCtx tm
      sTy ← showTermCtx ty
      sTyInf ← showTermCtx tyinf
      fail (sTm ++ " has type " ++ sTyInf ++ " but was expected to have type " ++ sTy)

checkElim :: Ind Ty → Lvl → InCtx ()
checkElim ind lvl =
  if arSort (indArity ind) /= Prop || lvl == Prop
  then pure ()
  else
    let msg = "Can't eliminate from Prop into " ++ show lvl ++ " for types not meeting the subsingleton criterion" in
      case indConstructors ind of
        [] → pure ()
        [cst] → isolate $
               do
                 { let params = indParams ind
                 ; paramNames ← addTelescope params
                 ; let args = csArgs cst
                 ; argNames ← aux paramNames (csArgs cst) []
                 ; let retIndices = instantiate (FVar <$> (argNames ++ paramNames)) <$> csResIndices cst
                 ; normIndices ← mapM whnf retIndices
                 ; mapM (\ name → 
                           do
                             { ty ← infer (FVar name)
                             ; u ← infer ty
                             ; lvl ← whnf u >>= asU
                             ; if lvl == Prop
                               then pure ()
                               else if FVar name `elem` normIndices then pure ()
                               else fail msg
                             }
                        ) argNames
                 ; pure ()
                 }
        _ → fail msg
  where
    aux :: [Name] → [(Name, CsArg Ty)] → [Name] → InCtx [Name]
    aux _ [] csArgNames = pure csArgNames
    aux paramNames ((argName, arg):args) csArgNames =
      do
        argType ← csArgType ind paramNames csArgNames arg
        argName' ← addVar argName argType
        aux paramNames args (argName':csArgNames)

ensureType :: Ty → InCtx ()
ensureType ty =
  do
    u ← infer ty
    whnf u >>= asU
    pure ()
