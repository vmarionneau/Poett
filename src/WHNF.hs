{-# LANGUAGE UnicodeSyntax #-}

module WHNF (module WHNF) where

import Name
import Ind
import Term
import Ctx
import Elim

-- Pop at most 'depth' abstractions from a term
unravelAbs :: Int → Tm → ([(Name, Ty)], Tm)
unravelAbs 0 tm = ([], tm)
unravelAbs depth (Abs name ty tm) =
  let (names, tm') = unravelAbs (depth - 1) tm
  in ((name,ty):names, tm')
unravelAbs _ tm = ([], tm)

whnf :: Tm → InCtx Tm
whnf (App l []) = whnf l
whnf (App l r) =
  do
    l' ← whnf l
    case l' of
      Abs _ _ _ →
        let (names, tm) = unravelAbs (length r) l' in
        let args = take (length names) r in
        let remain = drop (length names) r in
          whnf (App (instantiate (reverse args) tm) remain)
      App l'' r' → whnf (App l'' (r' ++ r)) 
      Elim lvl nameInd →
        do
          { ind ← getInd nameInd
          ; let len = elimArgLength ind
          ; if length r >= len
            then
              do
                { let args = take (indParamLength ind + 1 + (length $ indConstructors ind)) r
                ; cst ← inCtxOfMaybe "Error : length of arguments of elim is too small" $ r `atMay` (len - 1)
                ; cst' ← whnf cst
                ; let stuckRes =  App (Elim lvl nameInd) (take (len - 1) r ++ cst':drop len r)
                ; case asApp cst' of
                    (Constr nameInd' i, cargs) →
                      if nameInd' == nameInd
                      then
                        do
                          { constr ← getConstr ind i
                          ; rule ← constrElimRule ind lvl i
                          ; if length cargs == indParamLength ind + length (csArgs constr)
                            then whnf $ App (instantiate ((reverse $ drop (indParamLength ind) cargs) ++ reverse args) rule) (drop len r)
                            else pure stuckRes  
                          }
                      else pure stuckRes
                    _ → pure stuckRes
                }
            else pure $ App (Elim lvl nameInd) r
          }
      Cast l'' _ → whnf (App l'' r)
      _ → pure $ App l' r
whnf (Let _ _ tm1 tm2) = whnf (instantiate [tm1] tm2)
whnf (Cast tm ty) =
  do tm' ← whnf tm
     pure $ Cast tm' ty
whnf (FVar name) =
  do
    entry ← getLocal name
    case entryDef entry of
      Nothing → pure $ FVar name
      Just def → whnf def
whnf (Ident s) =
  do
    bdef ← isDef s
    if bdef
      then
      do
        { df ← getDef s
        ; case defBody df of
            Nothing → pure $ Ident s
            Just e → whnf e
        } 
      else pure $ Ident s
whnf t = pure t

hnf :: Tm → InCtx Tm
hnf tm = whnf tm >>= aux
  where
    aux (Pi name ty fam) =
      do
        ty' ← hnf ty
        name' ← addVar name ty'
        fam' ← hnf $ instantiate [FVar name'] fam
        closeProducts [name'] fam'
    aux (Abs name ty tm') =
      do
        ty' ← hnf ty
        name' ← addVar name ty'
        tm'' ← hnf $ instantiate [FVar name'] tm'
        closeAbs [name'] tm''
    aux (App tm' args) =
      do
        tm'' ← hnf tm'
        pure $ App tm'' args
    aux (Cast tm' ty) =
      do
        ty' ← hnf ty
        tm'' ← hnf tm'
        pure $ Cast tm'' ty'
    aux t = pure t

nf :: Tm → InCtx Tm
nf tm = whnf tm >>= aux
  where
    aux (Pi name ty fam) =
      do
        ty' ← nf ty
        name' ← addVar name ty'
        fam' ← nf $ instantiate [FVar name'] fam
        closeProducts [name'] fam'
    aux (Abs name ty tm') =
      do
        ty' ← nf ty
        name' ← addVar name ty'
        tm'' ← nf $ instantiate [FVar name'] tm'
        closeAbs [name'] tm''
    aux (App tm' args) =
      do
        tm'' ← nf tm'
        args' ← mapM nf args
        pure $ App tm'' args'
    aux (Cast tm' ty) =
      do
        ty' ← nf ty
        tm'' ← nf tm'
        pure $ Cast tm'' ty'
    aux t = pure t


isUnitLike :: Ty → InCtx Bool
isUnitLike (Pi name ty fam) =
  do
    name' ← addVar name ty
    b ← whnf (instantiate [FVar name'] fam) >>= isUnitLike
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
                  Just ty' → whnf ty' >>= isUnitLike
            else
              do
                ind ← getInd s
                if indIndices ind /= [] || length (indParams ind) /= length params
                  then pure False
                  else
                  case indConstructors ind of
                    [] → pure True
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
            b ← if argRec arg then pure False else whnf cty >>= isUnitLike
            name' ← addVar name cty
            aux params cargs $ (name', b):l

conv :: Tm → Tm → InCtx Bool
conv tml tmr =
  do
    tml' ← whnf tml
    tmr' ← whnf tmr
    aux tml' tmr'
  where
    aux (BVar i) (BVar j) = pure $ i == j
    aux (FVar name) (FVar name') =
      do
        entry ← getLocal name
        bUnit ← whnf (entryType entry) >>= isUnitLike
        pure $ name == name' || bUnit
    aux (U l) (U l') = pure $ l == l'
    aux (Ident s) (Ident s') = pure $ s == s'
    aux (Pi name ty fam) (Pi _ ty' fam') =
      do
        b1 ← conv ty ty'
        if b1
          then do
          { name' ← addVar name ty
          ; b2 ← conv (instantiate [FVar name'] fam) (instantiate [FVar name'] fam')
          ; removeDecl name'
          ; pure b2
          }
          else pure False
    aux (Abs name ty tm) (Abs _ ty' tm') =
      do
        b1 ← conv ty ty'
        if b1
          then do
          { name' ← addVar name ty
          ; b2 ← conv (instantiate [FVar name'] tm) (instantiate [FVar name'] tm')
          ; removeDecl name'
          ; pure b2
          }
          else pure False
    -- Eta for product types
    aux (Abs name ty tm) tm' =
      do
        name' ← addVar name ty
        b ← conv (instantiate [FVar name'] tm) (App tm' [FVar name'])
        removeDecl name'
        pure b
    aux tm (Abs name' ty' tm') =
      do
        name'' ← addVar name' ty'
        b ← conv (App tm [FVar name'']) (instantiate [FVar name''] tm')
        removeDecl name''
        pure b
    aux (App tm args) (App tm' args') =
      do
        b1 ← conv tm tm'
        let b2 = length args == length args'
        b3s ← mapM (uncurry conv) $ zip args args'
        pure $ b1 && b2 && all id b3s 
    aux (Cast tm _) (Cast tm' _) = conv tm tm'
    aux (Constr nameInd i) (Constr nameInd' j) = pure $ i == j && nameInd == nameInd'
    aux (Elim lvl nameInd) (Elim lvl' nameInd') = pure $ lvl == lvl' && nameInd == nameInd'
    -- Eta for unit-like types
    aux (FVar name) _ =
      do
        entry ← getLocal name
        whnf (entryType entry) >>= isUnitLike
    aux _ (FVar name') =
      do
        entry ← getLocal name'
        whnf (entryType entry) >>= isUnitLike
    aux _ _ = pure False
