{-# LANGUAGE UnicodeSyntax #-}

module Ctx (module Ctx) where

import WHNF (STm, STy)
import Ind
import qualified Data.Map as Map
import Data.Maybe (isJust, isNothing)

data LocalCtxEntry = LocalCtxEntry {entryType :: STy,  entryDef :: Maybe STm}
  deriving (Eq, Show)

type LocalCtx = [LocalCtxEntry]

type DefCtx = Map.Map String (STm, STy)
type IndCtx = Map.Map String (Ind STy)

data GlobalCtx = GCtx {defCtx :: DefCtx, indCtx :: IndCtx}

data Ctx = Ctx {global :: GlobalCtx, local :: LocalCtx}

typeOfVar :: LocalCtx → Int → Maybe STy
typeOfVar [] _ = Nothing
typeOfVar (h : _) 0 = Just (entryType h)
typeOfVar (_ : ctx) i = typeOfVar ctx (i - 1)

addVar :: Ctx → STy → Ctx
addVar ctx ty = ctx {local = LocalCtxEntry ty Nothing : local ctx}

addLocalDef :: Ctx → STm → STy → Ctx
addLocalDef ctx tm ty = ctx {local = LocalCtxEntry ty (Just tm) : local ctx}

addGlobalDef :: Ctx → String → STm → STy → Ctx
addGlobalDef ctx name tm ty = ctx {global = (global ctx) {defCtx = Map.insert name (tm, ty) $ defCtx (global ctx)}}

lctxLookupTy :: Int → LocalCtx → Maybe STy
lctxLookupTy _ [] = Nothing
lctxLookupTy 0 (h:_) = Just (entryType h)
lctxLookupTy n (_:t) = lctxLookupTy (n - 1) t

ctxLookupVar :: Int → Ctx → Maybe STy
ctxLookupVar i ctx = lctxLookupTy i (local ctx)

lctxLookupDef :: Int -> LocalCtx → Maybe (STy, STm)
lctxLookupDef _ [] = Nothing
lctxLookupDef 0 (h:_) = (\ def -> (entryType h, def)) <$> entryDef h
lctxLookupDef n (_:t) = lctxLookupDef (n - 1) t

gctxLookupDef :: String → GlobalCtx → Maybe (STy, STm)
gctxLookupDef s ctx = Map.lookup s (defCtx ctx)

ctxLookupDef :: String -> Ctx -> Maybe (STm, STy)
ctxLookupDef s ctx = gctxLookupDef s (global ctx)

gctxLookupInd :: String -> GlobalCtx -> Maybe (Ind STy)
gctxLookupInd s ctx = Map.lookup s (indCtx ctx)

ctxLookupInd :: String -> Ctx -> Maybe (Ind STy)
ctxLookupInd s ctx = gctxLookupInd s (global ctx)
