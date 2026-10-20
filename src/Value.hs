{-# LANGUAGE UnicodeSyntax #-}

module Value (module Value) where

import Name
import Term

data Clos a = Clos { closTm :: a , closEnv :: [VTm]}
    deriving Eq


data VTm
  = VNe Ne VTy
  | VU Lvl
  | VPi Name VTy (Clos Ty)
  | VAbs Name VTy (Clos Ty)
  | VConstr String Int [VTm]
  deriving Eq

data Val = Val VTm VTy
  deriving Eq

data Ne
  = NeFVar Name
  | NeBVar Int
  | NeApp Ne [Val]
  | NeIdent String
  | NeElimPart Lvl String [Val]
  | NeElim Lvl String [Val] Ne
  deriving Eq

type VTy = VTm

        
