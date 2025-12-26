{-# LANGUAGE UnicodeSyntax #-}

module Typecheck (module Typecheck) where

import Name
import Ind
import Term
import Ctx
import Elim
import WHNF
import Control.Monad (foldM, void)

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
    argNames ← aux paramNames args []
    closeProducts (argNames ++ paramNames)
      $ App (Ident (indName ind))
      $ (FVar <$> reverse paramNames)
      ++ (instantiate (FVar <$> (argNames ++ paramNames)) <$> csResIndices cst)
      where
        aux :: [Name] → [(Name, CsArg Ty)] → [Name] → InCtx [Name]
        aux _ [] csArgNames = pure csArgNames
        aux paramNames ((argName, arg):args) csArgNames =
          do
            argType ← csArgType paramNames csArgNames arg
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
    tyinf ← infer $ instantiate [FVar letVar] tm2
    unfoldLocal letVar tyinf
infer (Ident s) =
  do
    bdef ← isDef s
    if bdef
      then defType <$> getDef s
      else getInd s >>= indType
infer (Abs name ty tm) =
  do
    ensureType ty
    var ← addVar name ty
    tyRes ← infer $ instantiate [FVar var] tm
    removeDecl var
    pure $ Pi var ty (abstract [var] tyRes)
infer (App tm args) =
  do
    ty ← infer tm
    foldM (\ aty arg →
              do
                (_, tyarg, tyres) ← whnf aty >>= asPi
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
    tyinf ← infer tm
    u ← infer ty >>= asU
    u' ← infer tyinf >>= asU
    ty'' ← nf ty
    tyinf'' ← nf tyinf
    sTm ← showTermCtx tm
    sTy ← showTermCtx ty''
    sTyInf ← showTermCtx tyinf''
    let failMsg = sTm ++ " has type " ++ sTyInf ++ " but was expected to have type " ++ sTy
    if u /= u'
      then fail failMsg
      else do
      ty' ← whnf ty
      tyinf' ← whnf tyinf
      b ← conv ty' tyinf'
      if b
        then pure ()
        else fail failMsg
      
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
                 ; argNames ← aux paramNames args []
                 ; let retIndices = instantiate (FVar <$> (argNames ++ paramNames)) <$> csResIndices cst
                 ; normIndices ← mapM whnf retIndices
                 ; void $
                   mapM (\ name → 
                           do
                             { ty ← infer (FVar name)
                             ; u ← infer ty
                             ; lvl' ← whnf u >>= asU
                             ; if lvl' == Prop
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
        argType ← csArgType paramNames csArgNames arg
        argName' ← addVar argName argType
        aux paramNames args (argName':csArgNames)

ensureType :: Ty → InCtx ()
ensureType ty =
  do
    u ← infer ty
    void $ whnf u >>= asU

showTermCtx :: Tm → InCtx String
showTermCtx (FVar name) = pure $ show name
showTermCtx (BVar i) = pure $ show i
showTermCtx (U lvl) = pure $ show lvl
showTermCtx (Pi name ty fam) =
  do
    sTy ← showTermCtx ty
    let isBound = occurs 0 fam
    let name' = if isBound
                then
                  if nameString name == "_"
                  then named "x"
                  else name
                else named "_"
    name'' ← addVar name' ty
    sFam ← showTermCtx (instantiate [FVar name''] fam)
    removeDecl name''
    if isBound
      then pure $ "Π(" ++ show name'' ++ " : " ++ sTy ++ ") " ++ sFam
      else pure $ sTy ++ " → " ++ sFam
showTermCtx (Abs name ty tm) =
  do
    sTy ← showTermCtx ty
    let isBound = occurs 0 tm
    let name' = if isBound
                then
                  if nameString name == "_"
                  then named "x"
                  else name
                else named "_"
    name'' ← addVar name' ty
    sTm ← showTermCtx (instantiate [FVar name''] tm)
    removeDecl name''
    pure $ "λ (" ++ show name'' ++ " : " ++ sTy ++ "), " ++ sTm
showTermCtx (Let name ty tm body) =
  do
    sTy ← showTermCtx ty
    sTm ← showTermCtx tm
    let isBound = occurs 0 body
    let name' = if isBound
                then
                  if nameString name == "_"
                  then named "x"
                  else name
                else named "_"
    name'' ← addVar name' ty
    sBody ← showTermCtx (instantiate [FVar name''] body)
    removeDecl name''
    pure $ "let " ++ show name'' ++ " : " ++ sTy ++ " := " ++ sTm ++ " in " ++ sBody
showTermCtx (App tm args) =
  do
    sTm ← bracketArg tm
    sArgs ← mapM bracketArg args
    pure $ sTm ++ " " ++ (intercalate " " $ sArgs)
    where
      bracketArg :: Tm → InCtx String
      bracketArg tm'@(Pi _ _ _) = showTermCtx tm' >>= \ sTm → pure $ "(" ++ sTm ++ ")"
      bracketArg tm'@(Abs _ _ _) = showTermCtx tm' >>= \ sTm → pure $ "(" ++ sTm ++ ")"
      bracketArg (App tm' []) = showTermCtx tm'
      bracketArg tm'@(App _ _) = showTermCtx tm' >>= \ sTm → pure $ "(" ++ sTm ++ ")"
      bracketArg tm'@(Let _ _ _ _) = showTermCtx tm' >>= \ sTm → pure $ "(" ++ sTm ++ ")"
      bracketArg tm' = showTermCtx tm'
showTermCtx (Ident name) = pure name
showTermCtx (Cast tm ty) =
  do
    sTm ← showTermCtx tm
    sTy ← showTermCtx ty
    pure $ "(" ++ sTm ++ " : " ++ sTy ++ ")"
showTermCtx tm@(Constr nameInd i) =
  do
    mCst ← inCtxTry $ getIndConstr nameInd i
    case mCst of
      Left _ → pure $ show tm
      Right cst → pure $ csName cst
showTermCtx (Elim lvl nameInd) = pure $ "elim " ++ show lvl ++ " " ++ nameInd

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

showIndCtx :: Ind Ty → InCtx String
showIndCtx ind =
  do
    let params = indParams ind
    paramNames ← addTelescope params
    showPs ← mapM (\name →
                     do
                       ty ← entryType <$> getLocal name
                       sTy ← showTermCtx ty
                       pure $ "(" ++ show name ++ " : " ++ sTy ++ ") "
                  ) paramNames
    showCs ← mapM (\i →
                      do
                        cst ← getConstr ind i
                        ty ← constrType' paramNames ind i
                        sTy ← showTermCtx ty
                        pure $ csName cst ++ " : " ++ sTy
                  ) $ [0.. length (indConstructors ind) - 1]
    arType ← arToType paramNames (indArity ind)
    sAr ← showTermCtx arType
    pure $ "ind " ++ indName ind ++ " " ++ concat showPs ++ ": " ++ sAr ++ (if showCs == [] then "" else "\n| " ++ intercalate "\n| " showCs)
