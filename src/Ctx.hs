{-# LANGUAGE UnicodeSyntax #-}

module Ctx (module Ctx) where

import Term (Tm, Ty, vars)
import Ind

data LocalCtxEntry = LocalCtxEntry {entryType :: Ty, entryDef :: Maybe Tm}
  deriving (Eq, Show)

type LocalCtx = [LocalCtxEntry]

data GlobalCtxEntry = GCDef String Tm Ty | GCInd (Ind Ty)
  deriving (Eq, Show)

type GlobalCtx = [GlobalCtxEntry]

data Ctx = Ctx {global :: GlobalCtx, local :: LocalCtx}

typeOfVar :: LocalCtx → Int → Maybe Ty
typeOfVar [] _ = Nothing
typeOfVar (h : _) 0 = Just (entryType h)
typeOfVar (_ : ctx) i = typeOfVar ctx (i - 1)

wellFormedLocal :: LocalCtx → Bool
wellFormedLocal [] = True
wellFormedLocal (LocalCtxEntry ty Nothing : ctx) = wellFormedLocal ctx && all (< length ctx) (vars ty)
wellFormedLocal (LocalCtxEntry ty (Just tm) : ctx) = wellFormedLocal ctx && all (< length ctx) (vars ty)
                                                     && all (< length ctx) (vars tm)

addVar :: Ctx → Ty → Ctx
addVar ctx ty = ctx {local = LocalCtxEntry ty Nothing : local ctx}

addLocalDef :: Ctx → Tm → Ty → Ctx
addLocalDef ctx tm ty = ctx {local = LocalCtxEntry ty (Just tm) : local ctx}

addGlobalDef :: Ctx → String → Tm → Ty → Ctx
addGlobalDef ctx name tm ty = ctx {global = GCDef name tm ty : global ctx}

lctxLookup :: Int → LocalCtx → Maybe LocalCtxEntry
lctxLookup _ [] = Nothing
lctxLookup 0 (h:_) = Just h
lctxLookup n (_:t) = lctxLookup (n - 1) t
