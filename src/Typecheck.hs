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
indType = arToType . indArity

csArgType :: CsArg STy -> STy
csArgType arg = foldr Pi (argRes arg) (argArgs arg)

constrType :: [STy] -> Constructor STy -> STy
constrType pars cs = foldr Pi (csResult cs) (pars ++ (csArgType <$> csArgs cs))

lctxToSubst :: LocalCtx -> [STm]
lctxToSubst = map (\ (i, entry) -> case (entryDef entry) of
                                     Nothing -> Var i
                                     Just def -> def
                                    ) . zip [0..]
ctxToSubst :: Ctx -> Subst
ctxToSubst ctx = Subst (lctxToSubst (local ctx)) (fst <$> (defCtx (global ctx)))

inCtx :: Ctx -> STm -> STm
inCtx ctx tm = ESubst (ctxToSubst ctx) tm

infer :: Ctx -> STm -> Either String STy
infer ctx tm = infer_ ctx (pushSubst tm)

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
infer_ ctx (App tm args) =
  do
    ty <- infer ctx tm
    foldM (\ aty arg ->
              do
                (tyarg, tyres) <- asPi (whnf aty)
                check ctx arg tyarg
                pure $ ESubst (Subst [arg] Map.empty) tyres
          ) (inCtx ctx ty) args
infer_ ctx (Cast tm ty) = check ctx tm ty >> pure ty
infer_ ctx (Constr ind i) =
  maybeEither ("Unknown constructor of " ++ indName ind ++ " : " ++ show i)
  (constrType (indParams ind) <$> indConstructors ind `atMay` i)
infer_ ctx (Elim ind) = Left "Eliminators yet to be implemented"
infer_ _ _ = Left "Can't infer abstractions"
        
check :: Ctx -> STm -> STy -> Either String ()
check ctx tm ty =
  do
    u <- infer ctx ty
    asU u
    check_ ctx (pushSubst tm) (whnf $ inCtx ctx ty)
    
check_ :: Ctx -> STm -> STy -> Either String ()
check_ ctx  (Abs tm) (Pi ty fam) =
  let ctx' = addVar ctx ty in
    check ctx' tm ty
check_ ctx tm@(Abs _) ty = Left (show tm ++ " is an abstraction but is expected to have type " ++ show ty)  
check_ ctx (Let ty1 tm1 tm2) ty =
  do
    check ctx tm1 ty1
    let ctx' = addLocalDef ctx tm1 ty1
    check ctx' tm2 ty
check_ ctx tm ty =
  do
    tyinf <- infer ctx tm
    if conv ty tyinf
    then pure ()
    else Left (show tm ++ " has type " ++ show tyinf ++ " but was expected to have type " ++ show ty)
