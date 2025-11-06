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
asU ty = fail $ "Expected universe got " ++ show ty

asPi :: Ty → InCtx (Name, Ty, Ty)
asPi (Pi name ty fam) = pure (name, ty, fam)
asPi ty = fail $ "Expected product got " ++ show ty 

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
infer (Elim lvl nameInd) = elimType nameInd lvl
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
    else fail (show tm ++ " has type " ++ show tyinf ++ " but was expected to have type " ++ show ty)
