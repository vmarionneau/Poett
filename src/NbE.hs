{-# LANGUAGE UnicodeSyntax #-}

module NbE (module NbE) where

import Ind
import Term
import Ctx
import Elim
import Value

eval :: [VTm] → Tm → InCtx VTm
eval _ (FVar x) = pure $ VNe (NeFVar x)
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
        ; case defBody df of
            Nothing → pure $ VNe $ NeIdent s
            Just e → eval env e
        } 
      else pure $ VNe $ NeIdent s
eval env (Cast tm _) = eval env tm
eval _ (Constr name i) = pure $ VConstr name i []
eval _ (Elim l name) = pure $ VNe (NeElimPart l name [])

app :: [VTm] → VTm → [VTm] → InCtx VTm
app _ tm [] = pure tm
app env (VNe ne) args = appNe env ne args
app _ (VConstr name i cargs) args = pure $ VConstr name i (cargs ++ args)
app _ (VAbs _ _ (Clos bod env')) args = appClos bod env' args
app _ _ _ = fail "Expected abstraction, constructor or neutral"

appClos :: Tm → [VTm] → [VTm] → InCtx VTm
appClos _ _ [] = fail "Closure expects at least one argument"
appClos tm env (arg:args) = 
  do
    vtm ← eval (arg:env) tm
    app env vtm args

appNe :: [VTm] → Ne → [VTm] → InCtx VTm
appNe _ (NeApp ne args) args' = pure $ VNe $ NeApp ne (args ++ args')
appNe env (NeElimPart l name args) args' = 
    do 
      ind ← getInd name
      let allArgs = args ++ args'
      let len = elimArgLength ind
      if length allArgs < len 
      then pure $ VNe (NeElimPart l name allArgs)
      else 
        do
          let argsElim = take (len - 1) allArgs
          let argsRest = drop len allArgs
          cst ← inCtxOfMaybe "Error : length of arguments of elim is too small" $ allArgs `atMay` (len - 1)
          case cst of 
            VNe ne → 
                (case argsRest of 
                    [] → pure $ VNe (NeElim l name argsElim ne)
                    _ → pure $ VNe (NeApp (NeElim l name argsElim ne) argsRest)
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
                        qcargs ← mapM quote cargs
                        let argsPref =  take (indParamLength ind + 1 + (length $ indConstructors ind)) argsElim
                        qargsPref ← mapM quote argsPref 
                        let tm = instantiate ((reverse $ drop (indParamLength ind) qcargs) ++ reverse qargsPref) rule
                        vtm ← eval env tm
                        app env vtm argsRest
                    }
            _ → fail "Error : Expected constructor or neutral when applying eliminator"

appNe _ ne args = pure $ VNe $ NeApp ne args

quote :: VTm → InCtx Tm
quote (VNe ne) = quoteNe ne
quote (VU l) = pure $ U l
quote (VPi name ty (Clos bod env)) = 
    do
     nty ← quote ty
     var ← addVar name nty
     vbod ← eval (VNe (NeFVar var) : env) bod
     qbod ← quote vbod
     closeProducts [var] qbod
quote (VAbs name ty (Clos bod env)) = 
    do
     nty ← quote ty
     var ← addVar name nty
     vbod ← eval (VNe (NeFVar var) : env) bod
     qbod ← quote vbod
     closeAbs [var] qbod
quote (VConstr name i args) = 
    do
      qargs ← mapM quote args
      pure $ App (Constr name i) qargs

quoteNe :: Ne → InCtx Tm
quoteNe (NeFVar name) = pure $ FVar name
quoteNe (NeBVar _) = fail "Quoting a bound variable should never happen"
quoteNe (NeApp ne args) = 
    do 
      qargs ← mapM quote args
      tm ← quoteNe ne
      case tm of 
        App f args' → pure $ App f (args' ++ qargs)
        _ → pure $ App tm qargs
quoteNe (NeIdent s) = pure $ Ident s
quoteNe (NeElimPart l name args) = 
     do
      qargs ← mapM quote args
      pure $ App (Elim l name) qargs
quoteNe (NeElim l name args ne) = 
     do
      qargs ← mapM quote args
      tm ← quoteNe ne
      pure $ App (Elim l name) (qargs ++ [tm])
 
