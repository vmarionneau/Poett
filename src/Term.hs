{-# LANGUAGE UnicodeSyntax #-}

module Term (module Term) where
import Name
import Ind
import Data.Maybe (fromMaybe)
import Data.List (elemIndex)

data Tm
  = FVar Name
  | BVar Int
  | U Lvl
  | Pi Name Ty Ty
  | Abs Name Ty Tm
  | App Tm [Tm]
  | Let Name Ty Tm Tm
  | Ident String
  | Cast Tm Ty
  | Constr String Int
  | Elim Lvl String
  deriving Eq

type Ty = Tm

atMay :: [a] -> Int -> Maybe a
atMay [] _ = Nothing
atMay (h:_) 0 = Just h
atMay (_:t) n = atMay t (n - 1)

instantiateOff :: Int → [Tm] → Tm → Tm
instantiateOff off vals (BVar i) =
  if i < off
  then BVar i
  else fromMaybe (BVar i) $ vals `atMay` (i - off)
instantiateOff off vals (Pi name ty fam) = Pi name (instantiateOff off vals ty) (instantiateOff (off + 1) vals fam)
instantiateOff off vals (Abs name ty tm) = Abs name (instantiateOff off vals ty) (instantiateOff (off + 1) vals tm)
instantiateOff off vals (App tm args) = App (instantiateOff off vals tm) (instantiateOff off vals <$> args)
instantiateOff off vals (Let name ty tm1 tm2) = Let name (instantiateOff off vals ty) (instantiateOff off vals tm1) (instantiateOff (off + 1) vals tm2)
instantiateOff off vals (Cast tm ty) = Cast (instantiateOff off vals tm) (instantiateOff off vals ty)
instantiateOff _ _ tm = tm


instantiate :: [Tm] → Tm → Tm
instantiate = instantiateOff 0
  
instantiateTele :: [Tm] → [(Name, Ty)] → [(Name, Ty)]
instantiateTele vals = aux 0
  where
    aux _ [] = []
    aux off ((name,ty):tys) = (name, instantiateOff off vals ty) : aux (off + 1) tys  

abstract :: [Name] → Tm → Tm
abstract names = aux 0
  where
    aux off (FVar name) = fromMaybe (FVar name) $ (BVar . (+ off)) <$> name `elemIndex` names
    aux off (Pi name ty fam) = Pi name (aux off ty) (aux (off + 1) fam)
    aux off (Abs name ty tm) = Abs name (aux off ty) (aux (off + 1) tm)
    aux off (App tm args) = App (aux off tm) (aux off <$> args)
    aux off (Let name ty tm1 tm2) = Let name (aux off ty) (aux off tm1) (aux (off + 1) tm2)
    aux off (Cast tm ty) = Cast (aux off tm) (aux off ty)
    aux _ tm = tm

substitute :: [(Name, Tm)] → Tm → Tm
substitute sbt = instantiate (snd <$> sbt) . abstract (fst <$> sbt)

intercalate :: [a] -> [[a]] -> [a]
intercalate _ [] = []
intercalate _ [h] = h
intercalate s (h:t) = h ++ s ++ intercalate s t

instance Show Tm where
  show (FVar name) = show name
  show (BVar i) = show i
  show (U lvl) = show lvl
  show (Pi name ty1 ty2) = "Π[" ++ show name ++ " : " ++ show ty1 ++ "]." ++ show ty2
  show (Abs name ty tm) = "λ[" ++ show name ++ " : " ++ show ty ++ "]." ++ show tm
  show (Let name ty tm1 tm2) = "let[" ++ show name ++ " : " ++ show ty ++ "] := " ++ show tm1 ++ " in " ++ show tm2
  show (Ident s) = s
  show (Cast tm ty) = "(" ++ show tm ++ " : " ++ show ty ++ ")"
  show (Constr ind i) ="cs{" ++ ind ++ "; " ++ show i ++ "}"
  show (Elim lvl ind) = "elim{" ++ ind ++ " ▸ " ++ show lvl ++ "}"
  show (App tm args) = bracketArg tm ++ " " ++ (intercalate " " $ bracketArg <$> args)
    where
      bracketArg :: Tm -> String
      bracketArg tm@(Abs _ _ _) = "(" ++ show tm ++ ")"
      bracketArg tm@(App _ _) = "(" ++ show tm ++ ")"
      bracketArg tm@(Let _ _ _ _) = "(" ++ show tm ++ ")"
      bracketArg tm = show tm

