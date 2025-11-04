module Typecheck (module Typecheck) where

import WHNF
import Ctx
import Ind
import Data.Maybe (fromMaybe)
import Control.Monad (foldM)
import qualified Data.Map as Map

maybeEither :: a -> Maybe b -> Either a b
maybeEither _ (Just x) = Right x
maybeEither y _ = Left y

piLvl :: Lvl -> Lvl -> Lvl
piLvl _ Prop = Prop
piLvl Prop (Type i) = Type i
piLvl (Type i) (Type j) = Type (i `max` j)

asU :: STm -> Either String Lvl
asU (U lvl) = pure lvl
asU ty = Left $ "Expected universe got " ++ show ty

asPi :: STy -> Either String (STy, STy)
asPi (Pi ty fam) = pure (ty, fam)
asPi ty = Left $ "Expected product got " ++ show ty 

arToType :: Arity STy -> STy
arToType ar = foldr Pi (U (arSort ar)) (arArgs ar)

indType :: Ind STy -> STy
indType ind = foldr Pi (arToType (indArity ind)) (indParams ind)

csArgType :: CsArg STy -> STy
csArgType arg = foldr Pi (argRes arg) (argArgs arg)

constrType :: [STy] -> Constructor STy -> STy
constrType pars cs = foldr Pi (csResult cs) (pars ++ (csArgType <$> csArgs cs))

typeElimType :: Lvl -> Ind STy -> STy
typeElimType lvl ind =
  let famType = foldr Pi (U lvl) (fullArgsFrom 0) in
  let patTypes = zipWith aux [0..] (indConstructors ind) in
  let res =
        foldr Pi
        (App (Var (indicesLen + length patTypes + 1)) (Var <$> reverse [0..indicesLen - 1 + 1]))
        (fullArgsFrom (length patTypes + 1)) in
  foldr Pi res (pars ++ famType:patTypes)
  where
    pars = indParams ind
    indices = arArgs (indArity ind)
    parLen = length pars
    indicesLen = length indices
    
    fullArgsFrom :: Int -> [STm]
    fullArgsFrom k =
      let parLow = k + indicesLen in
      let parHigh = k + indicesLen + parLen - 1in
      let inHigh = indicesLen - 1 in
        indices ++ [App (Ident (indName ind)) $
                    Var <$> (reverse [parLow..parHigh]
                             ++ reverse [0..inHigh])
                   ]
        
    aux :: Int -> Constructor STy -> STy
    aux i cs =
      let res = whnf (csResult cs) in
      let indices =
            if indicesLen <= 0
            then []
            else
              case res of
                App _ indcs -> drop (indParamLength ind) indcs
                _ -> error "Didn't reduce to an application of inductive type to parameters and indices"
      in
      let args' = argAux i 0 0 (csArgs cs) in
      let sftPars = Var <$> reverse [length args' + i + 1 .. length args' + i + 1 + parLen - 1] in
      let csArgs' = sftPars ++ ((\(k, _) -> Var $ length args' - 1 - k) <$> filter (\ (_,(_, b)) -> b) (zip [0..] args')) in
      let tyRes = App (Var (i + length args')) (indices ++ [App (Constr ind i) csArgs']) in
      foldr Pi tyRes (fst <$> args')

    argAux :: Int -> Int -> Int -> [CsArg STy] -> [(STy, Bool)] 
    argAux _ _ _ [] = []
    argAux i j k (arg:args) =
      if argRec arg
      then
        let absTys = argArgs arg in
        let res = whnf (argRes arg) in
        let indices =
              if indicesLen <= 0
              then []
              else
                case res of
                  App _ indcs -> drop (indParamLength ind) indcs
                  _ -> error "Didn't reduce to an application of inductive type to parameters and indices"
        in
        
        let tyRes = App (Var (i + j + k + length absTys + 1)) (indices ++ [Var 0]) in
        (bump 0 (i + j + 1) (csArgType arg), True):(foldr Pi tyRes (bump 0 (i + j + 1 + 1) <$> absTys), False):argAux i (j + 1) (k + 1) args
      else (bump 0 (i + j + 1) (csArgType arg), True):argAux i j (k + 1) args

propElimType :: Lvl -> Ind STy -> STy
propElimType _ _ = error "Prop eliminator types not yet defined"

elimType :: Lvl -> Ind STy -> STy
elimType lvl ind =
  case arSort (indArity ind) of
    Prop -> propElimType lvl ind
    Type _ -> typeElimType lvl ind

lctxToSubst :: LocalCtx -> SubstV
lctxToSubst = aux . zip [0..] 
  where
    aux [] = Empty
    aux ((i,h):t) =
      case (entryDef h) of
        Nothing -> Bind (Var i) (aux t)
        Just def -> Bind def (aux t)

ctxToSubst :: Ctx -> Subst
ctxToSubst ctx = Subst (lctxToSubst (local ctx)) (fst <$> (defCtx (global ctx)))

inCtx :: Ctx -> STm -> STm
inCtx ctx tm = ESubst (ctxToSubst ctx) tm

infer :: Ctx -> STm -> Either String STy
infer ctx tm = clean <$> infer_ ctx (pushSubst tm)

infer_ :: Ctx -> STm -> Either String STy
infer_ ctx (Var i) = maybeEither ("Unbound variable " ++ show i) (bump 0 (i + 1) <$> ctxLookupVar i ctx)
infer_ _ (U Prop) = pure $ U (Type 0)
infer_ _ (U (Type i)) = pure $ U (Type (i + 1))
infer_ ctx (Pi ty fam) =
  do u <- infer ctx ty
     lvl <- asU (whnf u)
     let ctx' = addVar ctx ty
     u' <- infer ctx' fam
     lvl' <- asU (whnf $ inCtx ctx' u')
     pure $ U (piLvl lvl lvl')
infer_ ctx (Let ty tm1 tm2) =
  do
    check ctx tm1 ty
    let ctx' = addLocalDef ctx tm1 ty
    infer ctx' tm2
infer_ ctx (Ident s) =
  case ctxLookupDef s ctx of
    Just (_, ty) -> pure ty
    Nothing -> maybeEither ("Unknown identifier : " ++ s) (indType <$> ctxLookupInd s ctx)
infer_ ctx (Abs ty tm) =
    do u <- infer ctx ty
       lvl <- asU (whnf u)
       let ctx' = addVar ctx ty
       tyRes <- infer ctx' tm
       pure $ Pi ty tyRes
infer_ ctx (App tm args) =
  do
    ty <- infer ctx tm
    foldM (\ aty arg ->
              do
                (tyarg, tyres) <- asPi (whnf aty)
                check ctx arg tyarg
                pure $ ESubst (Subst (substSingleton arg) Map.empty) tyres
          ) (inCtx ctx ty) args
infer_ ctx (Cast tm ty) = check ctx tm ty >> pure ty
infer_ ctx (Constr ind i) =
  maybeEither ("Unknown constructor of " ++ indName ind ++ " : " ++ show i)
  (constrType (indParams ind) <$> indConstructors ind `atMay` i)
infer_ ctx (Elim lvl ind) = pure $ elimType lvl ind
infer_ _ tm@(ESubst _ _) = Left $ "infer_ was called with an explicit substitution, got : " ++ show tm
        
check :: Ctx -> STm -> STy -> Either String ()
check ctx tm ty =
  do
    u <- infer ctx ty
    asU (whnf u)
    tyinf <- infer ctx tm
    if conv ty tyinf
    then pure ()
    else Left (show tm ++ " has type " ++ show tyinf ++ " but was expected to have type " ++ show ty)

testCtx =
  Ctx
  (GCtx Map.empty
   (Map.fromList [("nat", nat), ("list", list), ("eq", eq)]))
  []
