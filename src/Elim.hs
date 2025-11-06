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

csArgType :: Lvl → Ind Ty → [Name] → [Name] → CsArg Ty → InCtx Ty
csArgType lvl ind paramNames csArgNames arg =
  do
    let args = instantiateTele (FVar <$> (csArgNames ++ paramNames)) $ argArgs arg
    argNames ← addTelescope args
    let resArgTy = instantiate (FVar <$> (argNames ++ csArgNames ++ paramNames)) (argRes arg)
    closeProducts argNames resArgTy
    
csRecArgMotive :: Lvl → Ind Ty → [Name] → Name → [Name] → Name → CsArg Ty → InCtx Ty
csRecArgMotive lvl ind paramNames famName csArgNames nonrec arg =
  do
    let args = instantiateTele (FVar <$> (csArgNames ++ paramNames)) $ argArgs arg
    argNames ← addTelescope args
    entry ← getLocal nonrec
    case asApp (snd $ (unravelPi (-1) $ entryType entry)) of
      (Ident nameInd, args) →
        if nameInd /= indName ind
        then fail "Return type of argument labeled recursive is not recursive"
        else do
          { let indices = instantiate (FVar <$> argNames) <$> drop (indParamLength ind) args
          ; let resRecTy = App (FVar famName) (indices ++ [App (FVar nonrec) $ FVar <$> reverse argNames])
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
            nonRecType ← csArgType lvl ind paramNames csArgNames arg
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
  do
    ind ← getInd nameInd
    let params = indParams ind
    paramNames ← addTelescope params
    famTy ← elimFam lvl ind paramNames
    famName ← addVar (Name "T" (-1)) famTy
    motives ← mapM (\ i → (constrMotive lvl ind paramNames famName i) >>=
                     \ ty → getConstr ind i >>=
                      \ cs → pure (Name ("P" ++ csName cs) (-1), ty))
              $ reverse  [0..length (indConstructors ind) - 1]
    motiveNames ← addVars motives
    let indices = instantiateTele (FVar <$> paramNames) $ indIndices ind
    indicesNames ← addTelescope indices
    let famArgTy = App (Ident (indName ind)) $ FVar <$> (reverse paramNames ++ reverse indicesNames)
    famArgName ← addVar (Name "x" (-1)) famArgTy
    closeProducts
      (famArgName:indicesNames ++ motiveNames ++ famName:paramNames)
      (App (FVar famName) $ FVar <$> (indicesNames ++ [famArgName]))

constrElimRule :: String → Lvl → Int → InCtx Tm
constrElimRule nameInd lvl i =
  isolate $
  do
    ind ← getInd nameInd
    cst ← getConstr ind i
    {- elim A0 A1 A2 ... T m0 m1 m2 ... I0 I1 I2 ... (C_i A0 A1 A2 ... x0 x1 x2 ...)
       --> m_i I0 I1 I2 ...
             x0 (λ y0 y1 y2 ..., elim A0 A1 A2 ... T m0 m1 m2 ... J00 J01 J02 ... (x0 y0 y1 y2 ...))
             x1 (λ y0 y1 y2 ..., elim A0 A1 A2 ... T m0 m1 m2 ... J10 J11 J12 ... (x1 y0 y1 y2 ...))
             ...
   -}
    let params = indParams ind
    paramNames ← addTelescope params
    famTy ← elimFam lvl ind paramNames
    famName ← addVar (Name "T" (-1)) famTy
    motives ← mapM (\ i → (constrMotive lvl ind paramNames famName i) >>=
                     \ ty → getConstr ind i >>=
                      \ cs → pure (Name ("P" ++ csName cs) (-1), ty))
              $ reverse  [0..length (indConstructors ind) - 1]
    motiveNames ← addVars motives
    let args = csArgs cst
    motive ← inCtxOfMaybe ("Unbound constructor for inductive " ++ indName ind ++ " : " ++ show i) $ (reverse motiveNames) `atMay` i
    (csArgNames, motiveArgs) ← aux ind paramNames famName motiveNames args [] []
    pure $ abstract (csArgNames ++ motiveNames ++ famName:paramNames) (App (FVar motive) (reverse motiveArgs))
      where
        aux :: Ind Ty → [Name] → Name → [Name] → [(Name, CsArg Ty)] → [Name] → [Tm] → InCtx ([Name], [Tm])
        aux _ _ _ _ [] csArgNames tms = pure (csArgNames, tms)
        aux ind paramNames famName motiveNames ((argName, arg):args) csArgNames tms =
          let aux' = aux ind paramNames famName motiveNames in
          do
            nonRecType ← csArgType lvl ind paramNames csArgNames arg
            nonRec ← addVar argName nonRecType
            if argRec arg then
              do
                { let args' = instantiateTele (FVar <$> (csArgNames ++ paramNames)) $ argArgs arg
                ; argNames ← addTelescope args'
                ; entry ← getLocal nonRec
                ; case asApp (snd $ (unravelPi (-1) $ entryType entry)) of
                    (Ident nameInd, resArgs) →
                      if nameInd /= indName ind
                      then fail "Return type of argument labeled recursive is not recursive"
                      else do
                        { let argIndices = instantiate (FVar <$> argNames) <$> drop (indParamLength ind) resArgs
                        ; ih ← closeAbs argNames
                               $ App (Elim lvl (indName ind))
                               $ (FVar <$> (reverse paramNames ++ famName:reverse motiveNames))
                                  ++ argIndices
                                  ++ [App (FVar nonRec) $ FVar <$> (reverse argNames)]
                        ; aux' args (nonRec:csArgNames) (ih:(FVar nonRec):tms)
                        }
                    _ → fail "Return type of argument labeled recursive is not recursive"
                }
            else aux' args (nonRec:csArgNames) (FVar nonRec:tms)
   

