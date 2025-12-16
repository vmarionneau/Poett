module TestInds (module TestInds) where

import Name
import Ind
import Term
import Ctx
import qualified Data.Map as Map

z :: Constructor Ty
z = Constructor "O" [] []

sucArg :: CsArg Ty
sucArg = CsArg [] (Ident "nat") True 

suc :: Constructor Ty
suc = Constructor "S" [(Name "n" (-1), sucArg)] []

natAr :: Arity Ty
natAr = Arity [] (Type 0)

nat :: Ind Ty
nat = Ind "nat" [] natAr [z, suc]

nil :: Constructor Ty
nil = Constructor "nil" [] []

consArg1 :: CsArg Ty
consArg1 = CsArg [] (BVar 0) False

consArg2 :: CsArg Ty
consArg2 = CsArg [] (App (Ident "list") [BVar 1]) True

cons :: Constructor Ty
cons = Constructor "cons" [(Name "h" (-1) , consArg1), (Name "t" (-1), consArg2)] []

listAr :: Arity Ty
listAr = Arity [] (Type 0)

list :: Ind Ty
list = Ind "list" [(Name "A" (-1), U (Type 0))] natAr [nil, cons]

refl :: Constructor Ty
refl = Constructor "refl" [] [BVar 0]

eqAr :: Arity Ty
eqAr = Arity [(Name "y" (-1), BVar 1)] Prop

eq :: Ind Ty
eq = Ind "eq" [(Name "A" (-1), U (Type 0)), (Name "x" (-1), BVar 0)] eqAr [refl]

orlArg :: CsArg Ty
orlArg = CsArg [] (BVar 1) False

orl :: Constructor Ty
orl = Constructor "orl" [(named "a", orlArg)] []

orrArg :: CsArg Ty
orrArg = CsArg [] (BVar 0) False

orr :: Constructor Ty
orr = Constructor "orr" [(named "b", orrArg)] []

orAr :: Arity Ty
orAr = Arity [] Prop

orI :: Ind Ty
orI = Ind "or" [(named "A", U Prop), (named "B", U Prop)] orAr [orl, orr]

accArg1 :: CsArg Ty
accArg1 = CsArg [] (BVar 1) False

accArg2 :: CsArg Ty
accArg2 = CsArg [(named "y", BVar 2), (named "lt", App (BVar 2) [BVar 0, BVar 1])] (App (Ident "Acc") [BVar 4, BVar 3, BVar 1]) True

acc :: Constructor Ty
acc = Constructor "acc" [(named "x", accArg1), (named "below", accArg2)] [BVar 1]

accAr :: Arity Ty
accAr = Arity [(named "x", BVar 1)] Prop

accT :: Ind Ty
accT = Ind "Acc" [(named "A", U (Type 0)), (named "R", Pi (named "x") (BVar 0) $ Pi (named "y") (BVar 1) $ U Prop)] accAr [acc]

testIndCtx :: Ctx
testIndCtx = emptyCtx {global = emptyGlobalCtx {indCtx = Map.fromList [("nat", nat), ("list", list), ("eq", eq), ("or", orI), ("Acc", accT)]}} 

zero :: Tm
zero = Constr "nat" 0

sc :: Tm
sc = Constr "nat" 1

double :: Tm
double = App (Elim (Type 0) "nat")
         [ Abs (named "n") (Ident "nat") (Ident "nat")
         , zero
         , Abs (named "n") (Ident "nat") $
           Abs (named "IHn") (Ident "nat") (App sc [App sc [BVar 0]])
         ]
deepId :: Tm
deepId = App (Elim (Type 0) "nat")
         [ Abs (named "n") (Ident "nat") (Ident "nat")
         , zero
         , Abs (named "n") (Ident "nat") $
           Abs (named "IHn") (Ident "nat") (App sc [BVar 0])
         ]
add :: Tm
add = App (Elim (Type 0) "nat")
      [ Abs (named "n") (Ident "nat")
        (Pi (named "m") (Ident "nat") (Ident "nat"))
        
      , Abs (named "n") (Ident "nat") (BVar 0)
      , Abs (named "n") (Ident "nat")
        (Abs (named "f") (Pi (named "m") (Ident "nat") (Ident "nat"))
         (Abs (named "k") (Ident "nat")
          (App sc [App (BVar 1) [BVar 0]])))
      ] 

natDef :: String
natDef = unlines
         [ "ind nat : U₀\n"
         , "| zero : nat\n"
         , "| succ : Π(_ : nat) nat"
         ]

listDef :: String
listDef = unlines
          [ "ind list (A : U₀) : U₀\n"
          , "| nil : list A\n"
          , "| cons : Π(h : A) Π(t : list A) list A"
          ]

accDef :: String
accDef = unlines
         [ "ind Acc (A : U₀) (R : Π(_ : A) Π(_ : A) Prop) : Π(_ : A) Prop\n"
         , "| acc : Π(x : A) Π(below : Π(y : A) Π(_ : R y x) Acc A R y) Acc A R x"
         ]

wrongDef :: String
wrongDef = unlines
         [ "ind wrong : U₀\n"
         , "| csWrong : Π(x : U₀) wrong"
         ]
