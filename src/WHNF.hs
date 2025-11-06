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
whnf (App l r@(hr:tr)) =
  do
    l' ← whnf l
    case l' of
      Abs _ ty tm →
        let (names, tm) = unravelAbs (length r) l' in
        let args = take (length names) r in
        let rem = drop (length names) r in
          whnf (App (instantiate (reverse args) tm) rem)
      App l' r' → whnf (App l' (r' ++ r)) 
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
                            then whnf $ instantiate ((reverse $ drop (indParamLength ind) cargs) ++ reverse args) rule
                            else pure stuckRes  
                          }
                      else pure stuckRes
                    _ → pure stuckRes
                }
            else pure $ App (Elim lvl nameInd) r
          }
      Cast l' _ -> whnf (App l' r)               
      l' -> pure $ App l' r
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
      then getDef s >>= (whnf . defBody)
      else pure $ Ident s
whnf t = pure t

hnf :: Tm -> InCtx Tm
hnf tm = whnf tm >>= aux
  where
    aux (Pi name ty fam) =
      do
        ty' ← hnf ty
        fam' ← hnf fam
        pure $ Pi name ty' fam
    aux (Abs name ty tm) =
      do
        ty' ← hnf ty
        tm' ← hnf tm
        pure $ Abs name ty' tm
    aux (App tm args) =
      do
        tm' ← hnf tm
        pure $ App tm' args
    aux (Cast tm ty) =
      do
        ty' ← hnf ty
        tm' ← hnf tm
        pure $ Cast tm' ty'
    aux t = pure t

nf :: Tm -> InCtx Tm
nf tm = whnf tm >>= aux
  where
    aux (Pi name ty fam) =
      do
        ty' ← nf ty
        fam' ← nf fam
        pure $ Pi name ty' fam
    aux (Abs name ty tm) =
      do
        ty' ← nf ty
        tm' ← nf tm
        pure $ Abs name ty' tm
    aux (App tm args) =
      do
        tm' ← nf tm
        args' ← mapM nf args
        pure $ App tm' args'
    aux (Cast tm ty) =
      do
        ty' ← nf ty
        tm' ← nf tm
        pure $ Cast tm' ty'
    aux t = pure t

conv :: Tm -> Tm -> InCtx Bool
conv tm tm' =
  do
    tm0 ← whnf tm
    tm'0 ← whnf tm'
    aux tm0 tm'0
  where
    aux (BVar i) (BVar j) = pure $ i == j
    aux (FVar name) (FVar name') = pure $ name == name'
    aux (U l) (U l') = pure $ l == l'
    aux (Ident s) (Ident s') = pure $ s == s'
    aux (Pi _ ty fam) (Pi _ ty' fam') =
      do
        b1 ←  conv ty ty'
        b2 ← conv fam fam'
        pure $ b1 && b2
    aux (Abs _ _ tm) (Abs _ _ tm') = conv tm tm'
    aux (App tm args) (App tm' args') =
      do
        b1 ← conv tm tm'
        let b2 = length args == length args'
        b3s ← mapM (uncurry conv) $ zip args args'
        pure $ b1 && b2 && all id b3s 
    aux (Cast tm ty) (Cast tm' ty') = conv tm tm'
    aux (Constr nameInd i) (Constr nameInd' j) = pure $ i == j && nameInd == nameInd'
    aux (Elim lvl nameInd) (Elim lvl' nameInd') = pure $ lvl == lvl' && nameInd == nameInd'
    aux _ _ = pure False
