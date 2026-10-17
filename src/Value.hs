{-# LANGUAGE UnicodeSyntax #-}

module Value (module Value) where

import Name
import Term

data Clos a = Clos { closTm :: a , closEnv :: [VTm]}
    deriving Eq

data VTm
  = VNe Ne
  | VU Lvl
  | VPi Name VTy (Clos Ty)
  | VAbs Name VTy (Clos Ty)
  | VConstr String Int [VTm]
  deriving Eq

data Ne
  = NeFVar Name
  | NeBVar Int
  | NeApp Ne [VTm]
  | NeIdent String
  | NeElimPart Lvl String [VTm]
  | NeElim Lvl String [VTm] Ne
  deriving Eq

type VTy = VTm

        
