{-# LANGUAGE UnicodeSyntax #-}

module NbE (module NbE) where

import Term
import Ind
import IndUtils
import Ctx
import Elim
import Value

eval :: [VTm] → Tm → InCtx VTm
eval env (FVar x) =
    do
      entry ← getLocal x
      let ty = entryType entry
      vty ← eval env ty
      case entryDef entry of
        Nothing → pure $ VNe (NeFVar x) vty
        Just def → eval env def
eval env (BVar x) = inCtxOfMaybe "Variable not in scope" $ env `atMay` x
eval _ (U l) = pure $ VU l
eval env (Pi name ty bod) =
    do
      vty ← eval env ty
      pure $ VPi name vty (Clos bod env)
eval env (Abs name ty bod) =
    do
      vty ← eval env ty
      pure $ VAbs name vty (Clos bod env)
eval env (App tm []) = eval env tm
eval env (App tm args) =
    do
      vtm ← eval env tm
      vargs ← mapM (eval env) args
      app env vtm vargs
eval env (Let _ _ tm bod) =
    do
      vtm ← eval env tm
      eval (vtm:env) bod
eval env (Ident s) =
    do
      bdef ← isDef s
      if bdef then
        do
        { df ← getDef s
        ; let ty = defType df
        ; vty ← eval env ty
        ; case defBody df of
            Nothing → pure $ VNe (NeIdent s) vty
            Just e → eval env e
        }
      else
        do
          ind ← getInd s
          ty ← indType ind
          vty ← eval env ty
          pure $ VNe (NeIdent s) vty
eval env (Cast tm _) = eval env tm
eval _ (Constr name i) = pure $ VConstr name i []
eval env (Elim l name) =
    do
      ind ← getInd name
      ty ← elimType ind l
      vty ← eval env ty
      pure $ VNe (NeElimPart l name []) vty

app :: [VTm] → VTm → [VTm] → InCtx VTm
app _ tm [] = pure tm
app env (VNe ne vty) args = appNe env vty ne args
app _ (VConstr name i cargs) args = pure $ VConstr name i (cargs ++ args)
app _ (VAbs _ _ (Clos bod env')) args = appClos bod env' args
app _ _ _ = fail "Expected abstraction, constructor or neutral"

appClos :: Tm → [VTm] → [VTm] → InCtx VTm
appClos _ _ [] = fail "Closure expects at least one argument"
appClos tm env (arg:args) =
  do
    vtm ← eval (arg:env) tm
    app env vtm args

compNeArgs :: VTy → [VTm] → InCtx ([Val], VTy)
compNeArgs ty args = aux ty args []
    where
      aux vty [] vargs = pure $ (reverse vargs, vty)
      aux (VPi _ tyd (Clos bod env)) (vtm:vtms) vargs =
        do
          vty' ← eval (vtm:env) bod
          aux vty' vtms (Val vtm tyd : vargs)
      aux _ _ _ = fail $ "Expected product type when applying neutral"

compConstrArgsTy :: String → Int → [VTm] → InCtx ([Val], VTy)
compConstrArgsTy nameInd i args =
    do
      ind ← getInd nameInd
      ty ← constrType ind i
      vty ← eval [] ty
      compNeArgs vty args

appNe :: [VTm] → VTy → Ne → [VTm] → InCtx VTm
appNe _ vty (NeApp ne args) args' =
    do
      (argsVal, vty') ← compNeArgs vty args'
      pure $ VNe (NeApp ne (args ++ argsVal)) vty'
appNe env vty (NeElimPart l name args) args' =
    do
      ind ← getInd name
      (argsVal, vty') ← compNeArgs vty args'
      let allArgs = args ++ argsVal
      let len = elimArgLength ind
      if length allArgs < len
      then pure $ VNe (NeElimPart l name allArgs) vty'
      else
        do
          let argsElim = take (len - 1) allArgs
          let argsRest = drop len allArgs
          Val cst _ ← inCtxOfMaybe "Error : length of arguments of elim is too small" $ allArgs `atMay` (len - 1)
          case cst of
            VNe ne _ →
                (case argsRest of
                    [] → pure $ VNe (NeElim l name argsElim ne) vty'
                    _ → pure $ VNe (NeApp (NeElim l name argsElim ne) argsRest) vty'
                )
            VConstr name' i cargs →
                if name /= name' then fail "Error : Constructor of incorrect inductive is being eliminated"
                else
                  do
                    { constr ← getConstr ind i
                    ; rule ← constrElimRule ind l i
                    ; if length cargs /= indParamLength ind + length (csArgs constr)
                    ; then fail ("Error : Constructor " ++ csName constr ++ " not applied to enough arguments to be eliminated (" ++ show (length cargs) ++ " / " ++ show (indParamLength ind + length (csArgs constr)))
                    ; else
                      do
                        (vcargs, _) ← compConstrArgsTy name' i cargs
                        qcargs ← mapM quoteVal vcargs
                        let argsPref =  take (indParamLength ind + 1 + (length $ indConstructors ind)) argsElim
                        qargsPref ← mapM quoteVal argsPref
                        let tm = instantiate ((reverse $ drop (indParamLength ind) qcargs) ++ reverse qargsPref) rule
                        vtm ← eval env tm
                        app env vtm ((\ x → let Val y _ = x in y) <$> argsRest)
                    }
            _ → fail "Error : Expected constructor or neutral when applying eliminator"

appNe _ vty ne args =
    do
      (args', vty') ← compNeArgs vty args
      pure $ VNe (NeApp ne args') vty'

dummyU :: Ty
dummyU = U (Type (-1))

dummyVU :: VTy
dummyVU = VU (Type (-1))

quoteVal :: Val → InCtx Tm
quoteVal (Val tm ty) = aux tm ty
    where
      aux (VU l) (VU _) = pure $ U l
      aux (VPi name vty (Clos bod env)) (VU _) =
          do
           nty ← aux vty dummyVU
           var ← addVar name nty
           vbod ← eval (VNe (NeFVar var) vty : env) bod
           qbod ← aux vbod dummyVU
           closeProducts [var] qbod
      aux vtm (VPi name vty (Clos cod env)) =
          do
           qty ← aux vty dummyVU
           var ← addVar name qty
           vbod ← app [] vtm [VNe (NeFVar var) vty]
           icod ← appClos cod env [VNe (NeFVar var) vty]
           qbod ← aux vbod icod
           closeAbs [var] qbod
      aux (VConstr name i args) _ =
          do
            (vargs, vty) ← compConstrArgsTy name i args
            qty ← aux vty dummyVU
            let (tys, _) = unravelPi (-1) qty
            names ← addTelescope tys
            qargs ← mapM quoteVal vargs
            let qtm = App (Constr name i) (qargs ++ (FVar <$> names))
            closeAbs names qtm
      aux (VNe ne vty) _ =
        do qty ← aux vty dummyVU
           b ← isUnitLike qty
           if b
           then unitLikeWitness qty
           else quoteNe ne
      aux _ _ = fail "Ill-typed quote"

quoteNe :: Ne → InCtx Tm
quoteNe (NeFVar name) = pure $ FVar name
quoteNe (NeBVar _) = fail "Quoting a bound variable should never happen"
quoteNe (NeApp ne args) =
    do
      qargs ← mapM quoteVal args
      tm ← quoteNe ne
      case tm of
        App f args' → pure $ App f (args' ++ qargs)
        _ → pure $ App tm qargs
quoteNe (NeIdent s) = pure $ Ident s
quoteNe (NeElimPart l name args) =
     do
      qargs ← mapM quoteVal args
      pure $ App (Elim l name) qargs
quoteNe (NeElim l name args ne) =
     do
      qargs ← mapM quoteVal args
      tm ← quoteNe ne
      pure $ App (Elim l name) (qargs ++ [tm])

norm :: Tm → Ty → InCtx Tm
norm tm ty =
    do
      vty ← eval [] ty
      vtm ← eval [] tm
      quoteVal (Val vtm vty)

normTy :: Ty → InCtx Ty
normTy ty =
    do
      vty ← eval [] ty
      quoteVal (Val vty dummyVU)

convTy :: Ty → Ty → InCtx Bool
convTy ty ty' =
    do
      vty ← eval [] ty
      vty' ← eval [] ty'
      nty ← quoteVal (Val vty dummyVU)
      nty' ← quoteVal (Val vty' dummyVU)
      pure $ nty == nty'

conv :: Tm → Tm → Ty → InCtx Bool
conv tm tm' ty =
    do
      vty ← eval [] ty
      vtm ← eval [] tm
      vtm' ← eval [] tm'
      ntm ← quoteVal (Val vtm vty)
      ntm' ← quoteVal (Val vtm' vty)
      pure $ ntm == ntm'

isUnitLike :: Ty → InCtx Bool
isUnitLike (Pi name ty fam) =
  do
    name' ← addVar name ty
    b ← norm (instantiate [FVar name'] fam) dummyU >>= isUnitLike
    removeDecl name'
    pure b
isUnitLike ty =
  do
    let (tm, params) = asApp ty
    case tm of
      Ident s →
        do
          { bdef ← isDef s
          ; if bdef
            then
              do
                df ← getDef s
                case defBody df of
                  Nothing → pure False
                  Just ty' → norm ty' dummyU >>= isUnitLike
            else
              do
                ind ← getInd s
                if indIndices ind /= [] || length (indParams ind) /= length params
                  then pure False
                  else
                  case indConstructors ind of
                    [cs] →
                      do
                      {
                      ; (names, bs) ← unzip <$> aux params (csArgs cs) []
                      ; removeDecls names
                      ; pure $ all (\ b → b) bs
                      }
                    _ → pure False
          }
      _ → pure False
      where
        aux _ [] l = pure l
        aux params ((name, arg):cargs) l =
          do
            let caArgs = instantiateTele (((FVar . fst) <$> l) ++ reverse params) $ argArgs arg
            argNames ← addTelescope caArgs
            let resArgTy = instantiate ((FVar <$> (argNames ++ (fst <$> l))) ++ reverse params) (argRes arg)
            cty ← closeProducts argNames resArgTy
            b ← if argRec arg then pure False else norm cty dummyU >>= isUnitLike
            name' ← addVar name cty
            aux params cargs $ (name', b):l

unitLikeWitness :: Ty → InCtx Tm
unitLikeWitness (Pi name ty fam) =
  do
    name' ← addVar name ty
    let ty' = instantiate [FVar name'] fam
    tm ← norm ty' dummyU >>= unitLikeWitness
    closeAbs [name'] tm
unitLikeWitness ty =
  do
    let (tm, params) = asApp ty
    case tm of
      Ident s →
        do
          { bdef ← isDef s
          ; if bdef
            then
              do
                df ← getDef s
                case defBody df of
                  Nothing → fail "Not a unit-like type"
                  Just ty' → norm ty' dummyU >>= unitLikeWitness
            else
              do
                ind ← getInd s
                if indIndices ind /= [] || length (indParams ind) /= length params
                then fail "Not a unit-like type"
                else
                  case indConstructors ind of
                    [cs] →
                      do
                      {
                      ; tms ← aux params (csArgs cs) []
                      ; pure $ App (Constr s 0 ) (params ++ tms)
                      }
                    _ → fail "Not a unit-like type"
          }
      _ → fail "Not a unit-like type"
      where
        aux _ [] tms = pure tms
        aux params ((_,arg):cargs) tms =
          do
            let caArgs = instantiateTele (tms ++ reverse params) $ argArgs arg
            argNames ← addTelescope caArgs
            let resArgTy = instantiate ((FVar <$> argNames) ++ tms ++ reverse params) (argRes arg)
            cty ← closeProducts argNames resArgTy
            tm ← if argRec arg then fail "Not a unit-like type" else norm cty dummyU >>= unitLikeWitness
            aux params cargs $ tm:tms


