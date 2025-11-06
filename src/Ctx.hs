{-# LANGUAGE UnicodeSyntax #-}

module Ctx (module Ctx) where

import Name
import Term
import Ind
import qualified Data.Map as Map
import Data.Map (( !? ))
import Data.Maybe (isJust, isNothing)
import Data.List (find, partition)
import Control.Monad (foldM)

data LocalCtxEntry = LocalCtxEntry {entryName :: Name, entryType :: Ty, entryDef :: Maybe Tm}
  deriving (Eq, Show)

type LocalCtx = [LocalCtxEntry]

emptyLocalCtx :: LocalCtx
emptyLocalCtx = []

data Def = Def {defName :: String, defType :: Ty, defBody :: Tm}
  deriving (Eq, Show)

type DefCtx = Map.Map String Def
type IndCtx = Map.Map String (Ind Ty)

emptyDefCtx :: DefCtx
emptyDefCtx = Map.empty

emptyIndCtx :: IndCtx
emptyIndCtx = Map.empty

data GlobalCtx = GCtx {defCtx :: DefCtx, indCtx :: IndCtx}
  deriving (Eq, Show)

emptyGlobalCtx :: GlobalCtx
emptyGlobalCtx = GCtx emptyDefCtx emptyIndCtx

data Ctx = Ctx {global :: GlobalCtx, local :: LocalCtx}
  deriving (Eq, Show)

emptyCtx :: Ctx
emptyCtx = Ctx emptyGlobalCtx emptyLocalCtx

newtype InCtx a = InCtx {runInCtx :: Ctx → Either String (Ctx, a)}

instance Functor InCtx where
  fmap f mx = InCtx (fmap (\ (ctx, a) → (ctx, f a)) . runInCtx mx)

instance Applicative InCtx where
  pure x = InCtx (\ ctx → Right (ctx, x))
                 
  mf <*> mx = InCtx (\ ctx → case runInCtx mf ctx of
                               Left err → Left err
                               Right (ctx', f) → (\ (ctx'', x) → (ctx'', f x)) <$> (runInCtx mx ctx')
                    )
              
instance Monad InCtx where
  mx >>= f = InCtx (\ ctx → case runInCtx mx ctx of
                               Left err → Left err
                               Right (ctx', x) → runInCtx (f x) ctx'
                   )

instance MonadFail InCtx where
  fail s = InCtx (const $ Left s)

maybeEither :: a -> Maybe b -> Either a b
maybeEither _ (Just x) = Right x
maybeEither y _ = Left y

inCtxOfEither :: Either String a → InCtx a
inCtxOfEither m = InCtx (\ ctx → (\ x → (ctx, x)) <$> m)

inCtxOfMaybe :: String → Maybe a → InCtx a
inCtxOfMaybe s m = inCtxOfEither $ maybeEither s m

getCtx :: InCtx Ctx
getCtx = InCtx (\ ctx → Right (ctx, ctx))

getLocalCtx :: InCtx LocalCtx
getLocalCtx = local <$> getCtx

getGlobalCtx :: InCtx GlobalCtx
getGlobalCtx = global <$> getCtx

getDefCtx :: InCtx DefCtx
getDefCtx = defCtx <$> getGlobalCtx

getIndCtx :: InCtx IndCtx
getIndCtx = indCtx <$> getGlobalCtx

setCtx :: Ctx → InCtx ()
setCtx ctx = InCtx (const $ Right (ctx, ()))

setLocalCtx :: LocalCtx → InCtx ()
setLocalCtx lctx =
  do ctx ← getCtx
     setCtx $ ctx { local = lctx }

setGlobalCtx :: GlobalCtx → InCtx ()
setGlobalCtx gctx =
  do ctx ← getCtx
     setCtx $ ctx { global = gctx }

setDefCtx :: DefCtx → InCtx ()
setDefCtx defs =
  do gctx ← getGlobalCtx
     setGlobalCtx $ gctx { defCtx = defs }

setIndCtx :: IndCtx → InCtx ()
setIndCtx inds =
  do gctx ← getGlobalCtx
     setGlobalCtx $ gctx { indCtx = inds }

getLocal :: Name → InCtx LocalCtxEntry
getLocal name =
  do
    lctx ← getLocalCtx
    case find (( == name ) . entryName) lctx of
      Nothing → fail $ "Unbound variable" ++ show name
      Just entry → pure entry

getDef :: String → InCtx Def
getDef s =
  do
    defs ← getDefCtx
    case defs !? s of
      Nothing → fail $ "Not defined : " ++ s
      Just def → pure def

getInd :: String → InCtx (Ind Ty)
getInd s =
  do
    inds ← getIndCtx
    case inds !? s of
      Nothing → fail $ "Not defined : " ++ s
      Just ind → pure ind

getConstr :: Ind Ty → Int → InCtx (Constructor Ty)
getConstr ind i = inCtxOfEither $
                  maybeEither
                  ("Unbound constructor for inductive " ++
                  (indName ind) ++ " : " ++ show i) $
                  (indConstructors ind) `atMay` i

getIndConstr :: String → Int → InCtx (Constructor Ty)
getIndConstr nameInd i =
  do
    ind ← getInd nameInd
    getConstr ind i
    
freshName :: Name → InCtx Name
freshName name =
  do lctx ← getLocalCtx
     pure $ fresh name $ entryName <$> lctx

addVar :: Name → Ty → InCtx Name
addVar name ty =
  do name' ← freshName name
     lctx ← getLocalCtx
     setLocalCtx $ LocalCtxEntry name' ty Nothing : lctx
     pure name'

addVars :: [(Name, Ty)] → InCtx [Name]
addVars vars =
  do entries ← mapM (\ (name, ty) →
                        (freshName name) >>=
                        \ name' →
                          pure (LocalCtxEntry name' ty Nothing)
                    ) vars
     lctx ← getLocalCtx
     setLocalCtx $ entries ++ lctx
     pure $ entryName <$> entries

addTelescope :: [(Name, Ty)] → InCtx [Name]
addTelescope tel =
  foldM (\ names (name, ty) →
           do
             let ty' = instantiate (FVar <$> names) ty
             addVar name ty'
             pure (name:names)
        ) [] tel

addLocal :: Name → Ty → Tm → InCtx Name
addLocal name ty tm =
  do name' ← freshName name
     lctx ← getLocalCtx
     setLocalCtx $ LocalCtxEntry name' ty (Just tm) : lctx
     pure name'

addLocals :: [(Name, Ty, Tm)] → InCtx [Name]
addLocals decls =
  do entries ← mapM (\ (name, ty, tm) →
                       (freshName name) >>=
                       \ name' →
                         pure (LocalCtxEntry name' ty (Just tm))
                    ) decls
     lctx ← getLocalCtx
     setLocalCtx $ entries ++ lctx
     pure $ entryName <$> entries

removeDecl :: Name → InCtx ()
removeDecl name =
  do
    lctx ← getLocalCtx
    if any (\ entry → entryName entry == name) lctx
    then setLocalCtx $ filter (\ entry → entryName entry /= name) lctx
    else fail $ "Can't remove bound variable " ++ show name ++ " it is not in context."

removeDecls :: [Name] → InCtx ()
removeDecls names =
  do
    lctx ← getLocalCtx
    let lctxNames = entryName <$> lctx
    if all (flip elem lctxNames) names
    then setLocalCtx $ filter (\ entry → not $ entryName entry `elem` names) lctx
    else fail $ "Can't remove bound variables " ++ intercalate "," (show <$> names) ++ " some (or all) of them are not in context."

closeProducts :: [Name] → Ty → InCtx Ty
closeProducts names ty =
  do
    lctx ← getLocalCtx
    let (vars, lctx') = partition (\ entry → entryName entry `elem` names) lctx
    let names' = entryName <$> vars
    setLocalCtx lctx'
    pure $ foldl (\ acc entry → Pi (entryName entry) (entryType entry) (abstract [entryName entry] acc)) ty vars

closeAbs :: [Name] → Tm → InCtx Tm
closeAbs names tm =
  do
    lctx ← getLocalCtx
    let (vars, lctx') = partition (\ entry → entryName entry `elem` names) lctx
    let names' = entryName <$> vars
    setLocalCtx lctx'
    pure $ foldl (\ acc entry → Pi (entryName entry) (entryType entry) (abstract [entryName entry] acc)) tm vars

isolate :: InCtx a → InCtx a
isolate m =
  do
    ctx ← getCtx
    x ← m
    setCtx ctx
    pure x
