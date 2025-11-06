{-# LANGUAGE UnicodeSyntax #-}

module Elim (module Elim) where
import Name
import Term
import Ind
import Ctx

-- Pop at most 'depth' products from a term
unravelPi :: Int → Tm → ([(Name, Ty)], Tm)
unravelPi 0 tm = ([], tm)
unravelPi depth (Pi name ty fam) =
  let (names, fam') = unravelPi (depth - 1) fam
  in ((name,ty):names, fam')
unravelPi _ tm = ([], tm)

asApp :: Tm -> (Tm, [Tm])
asApp (App tm args) = (tm, args)
asApp tm = (tm, [])

elimFam :: Lvl → Ind Ty → [Name] → InCtx Ty
elimFam lvl ind paramNames =
  do 
    let indices = instantiateTele (FVar <$> paramNames) $ indIndices ind
    indicesNames ← addTelescope indices
    let resIndTy = App (Ident (indName ind)) $ FVar <$> (reverse paramNames ++ reverse indicesNames)
    dummy ← freshName (Name "x" (-1))
    let ty = Pi dummy resIndTy (U lvl)
    closeProducts indicesNames ty

csArgMotive :: Lvl → Ind Ty → [Name] → Name → [Name] → CsArg Ty → InCtx Ty
csArgMotive lvl ind paramNames famName csArgNames arg =
  do
    let args = instantiateTele (FVar <$> paramNames) $ argArgs arg
    argNames ← addTelescope args
    let resArgTy = instantiate (FVar <$> (argNames ++ csArgNames ++ famName:paramNames)) (argRes arg)
    closeProducts argNames resArgTy
    
csRecArgMotive :: Lvl → Ind Ty → [Name] → Name → [Name] → Name → CsArg Ty → InCtx Ty
csRecArgMotive lvl ind paramNames famName csArgNames nonrec arg =
  do
    let args = instantiateTele (FVar <$> paramNames) $ argArgs arg
    argNames ← addTelescope args
    entry ← getLocal nonrec
    case asApp (snd $ (unravelPi (-1) $ entryType entry)) of
      (Ident nameInd, args) →
        if nameInd /= indName ind
        then fail "Return type of argument labeled recursive is not recursive"
        else do
          { 
            let indices = instantiate (FVar <$> argNames) <$> drop (indParamLength ind) args
          ; let resRecTy = App (FVar famName) (indices ++ [App (FVar nonrec) (FVar <$> reverse argNames)])
          ; closeProducts argNames resRecTy
          }
      _ → fail "Return type of argument labeled recursive is not recursive"
    
constrMotive :: Lvl → Ind Ty → [Name] → Name → Int → InCtx Ty
constrMotive lvl ind paramNames famName i =
  do
    cs ← getConstr ind i
    (csArgNames, allArgNames) ← aux (csArgs cs) [] []
    let resIndices = instantiate (FVar <$> (csArgNames ++ paramNames)) <$> (csResIndices cs)
    let resTy = App (FVar famName) (resIndices ++ [App (Constr (indName ind) i) $ FVar <$> (reverse paramNames ++ reverse csArgNames)])
    closeProducts allArgNames resTy
      where
        aux :: [(Name, CsArg Ty)] → [Name] → [Name] → InCtx ([Name], [Name])
        aux [] csArgNames allArgNames = pure (csArgNames, allArgNames)
        aux ((argName, arg):args) csArgNames allArgNames =
          do
            nonRecType ← csArgMotive lvl ind paramNames famName csArgNames arg
            nonRec ← addVar argName nonRecType
            if argRec arg then
              do
                { recType ← csRecArgMotive lvl ind paramNames famName csArgNames nonRec arg
                ; recName ← addVar (Name ("IH" ++ nameString argName) (-1)) recType
                ; aux args (nonRec:csArgNames) (recName:nonRec:allArgNames)
                }
            else aux args (nonRec:csArgNames) (nonRec:allArgNames)

elimType :: String → Lvl → InCtx Ty
elimType _ Prop = fail "TODO : Implement Prop elimination"
elimType nameInd lvl =
  isolate $
  do
    ind ← getInd nameInd
    let params = indParams ind
    paramNames ← addTelescope params
    famTy ← elimFam lvl ind paramNames
    famName ← addVar (Name "T" (-1)) famTy
    resTy ←
      isolate $
      do
        { let indices = instantiateTele (FVar <$> paramNames) $ indIndices ind
        ; indicesNames ← addTelescope indices
        ; let famArgTy = App (Ident (indName ind)) $ FVar <$> (reverse paramNames ++ reverse indicesNames)
        ; famArgName ← addVar (Name "x" (-1)) famArgTy
        ; closeProducts (famArgName:indicesNames) (App (FVar famName) $ FVar <$> (indicesNames ++ [famArgName]))
        }
    motives ← mapM (\ i → (constrMotive lvl ind paramNames famName i) >>=
                     \ ty → getConstr ind i >>=
                      \ cs → pure (Name ("P" ++ csName cs) (-1), ty))
              $ reverse  [0..length (indConstructors ind) - 1]
    motiveNames ← addVars motives
    closeProducts (motiveNames ++ famName:paramNames) resTy
    
    
       
   

{-
constrArgRule :: [Name] → [(Name, Ty)] → CsArg Ty → InCtx Tm
constrArgRule paramNames indices arg =
  isolate $
  do
    
constrElimRule :: String → Int → InCtx Tm
constrElimRule nameInd i =
  do
    ind ← getInd nameInd
    cst ← getConstr ind i
    let params = reverse $ indParams ind
    let indices = reverse $ indIndices ind
    let args = csArgs cst
    isolate $
      do
        paramNames ← addVars params
        motive ← addVar (Name "T", -1)
        constrArgRule

-}
