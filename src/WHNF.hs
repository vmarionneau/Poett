{-# LANGUAGE UnicodeSyntax #-}

module WHNF (module WHNF) where

{- import qualified Term as T (Tm, Ty) -}
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Ind

atMay :: [a] -> Int -> Maybe a
atMay [] _ = Nothing
atMay (h:_) 0 = Just h
atMay (_:t) n = atMay t (n - 1)

intercalate :: [a] -> [[a]] -> [a]
intercalate _ [] = []
intercalate _ [h] = h
intercalate s (h:t) = h ++ s ++ intercalate s t

-- Type of parallel substitutions
data Subst = Subst { vars :: [STm], idents :: Map.Map String STm }
  deriving Eq

data STm
  = Var Int
  | U Lvl
  | Pi STy STy
  | Abs STy STm
  | App STm [STm]
  | Let STy STm STm
  | Ident String
  | Constr (Ind STy) Int [STm]
  | Elim (Ind STy)
  | ESubst Subst STm
  deriving Eq

type STy = STm

instance Show Subst where
  show s = intercalate ";" $ (show <$> (vars s)) ++ ((\ (i, tm) -> show i ++ " := " ++ show tm) <$> (Map.toList $ idents s))

instance Show STm where
  show (Var i) = "x" ++ show i
  show (U Prop) = "Prop"
  show (U (Type i)) = "Type " ++ show i
  show (Pi ty1 ty2) = "Π(" ++ show ty1 ++ "). " ++ show ty2
  show (Abs ty tm) = "λ(" ++ show ty ++ "). " ++ show tm
  show (App tm args) = "(" ++ show tm ++ ")" ++ concatMap (\ a -> "(" ++ show a ++ ")") args
  show (Let ty tm1 tm2) = "let(" ++ show ty ++ ") := " ++ show tm1 ++ " in " ++ show tm2
  show (Ident s) = s
  show (Constr ind i args) =
    let dummy = "cs{" ++ indName ind ++ "; " ++ show i ++ "}"  in
    let name = fromMaybe dummy (csName <$> (indConstructors ind `atMay` i)) in
        name ++ concatMap (\ a -> "(" ++ show a ++ ")") args
  show (Elim ind) = "elim{" ++ indName ind ++ "}"
  show (ESubst s tm) = "(" ++ show tm ++ ")[" ++ show s ++ "]"

bump :: Int → Int → STm → STm
bump n k (Var i) =
  if i >= n
  then Var (i + k)
  else Var i
bump n k (U l) = U l
bump n k (Pi ty tm) = Pi (bump n k ty) (bump (n + 1) k tm)
bump n k (Abs ty tm) = Abs (bump n k ty) (bump (n + 1) k tm)
bump n k (App tm1 args) = App (bump n k tm1) (bump n k <$> args)
bump n k (Let ty tm1 tm2) = Let (bump n k ty) (bump n k tm1) (bump (n + 1) k tm2)
bump n k (Ident i) = Ident i
bump n k (Constr ind i args) = Constr ind i (bump n k <$> args)
bump n k (Elim ind) = Elim ind
bump n k (ESubst s tm) = ESubst (Subst (bump n k <$> vars s) (idents s)) (bump n k tm)

lift :: Subst → Subst
lift s = Subst (Var 0 : (bump 0 1 <$> vars s)) (idents s)

-- As we consider parallel substitutions, we have to compose the outer one on top of the terms of the inner one
composeSubst :: Subst → Subst → Subst
composeSubst outer inner = Subst ((ESubst outer <$> vars inner) ++ vars outer) (idents inner `Map.union` idents outer)

pushSubst :: STm → STm
pushSubst (ESubst sb t) = aux sb t
  where
    aux s (ESubst s' t') = aux (composeSubst s s') t'
    aux s (Var i) = fromMaybe (Var i) (vars s `atMay` i)
    aux _ (U l) = U l
    aux s (Pi ty tm) = Pi (ESubst s ty) (ESubst (lift s) tm)
    aux s (Abs ty tm) = Abs (ESubst s ty) (ESubst (lift s) tm)
    aux s (App tm1 args) = App (ESubst s tm1) (ESubst s <$> args)
    aux s (Let ty tm1 tm2) = Let (ESubst s ty) (ESubst s tm1) (ESubst (lift s) tm2)
    aux s (Ident i) = fromMaybe (Ident i) (idents s Map.!? i)
    aux s (Constr ind i args) = Constr ind i (ESubst s <$> args)
    aux _ (Elim ind) = Elim ind
pushSubst t = t 

execSubst :: STm → STm
execSubst t = aux (Subst [] Map.empty) t
  where
    aux s (ESubst s' t') = aux (composeSubst s s') t'
    aux s (Var i) = fromMaybe (Var i) (execSubst <$> vars s `atMay` i)
    aux _ (U l) = U l
    aux s (Pi ty tm) = Pi (aux s ty) (aux (lift s) tm)
    aux s (Abs ty tm) = Abs (aux s ty) (aux (lift s) tm)
    aux s (App tm1 args) = App (aux s tm1) (aux s <$> args)
    aux s (Let ty tm1 tm2) = Let (aux s ty) (aux s tm1) (aux (lift s) tm2)
    aux s (Ident i) = fromMaybe (Ident i) (idents s Map.!? i)
    aux s (Constr ind i args) = Constr ind i (aux s <$> args)
    aux _ (Elim ind) = Elim ind

dummyInd :: Ind STy -> Ind STy
dummyInd ind = Ind (indName ind) [] (Arity [] Prop) []

erase :: STm -> STm
erase (Pi ty tm) = Pi (erase ty) (erase tm)
erase (Abs ty tm) = Abs (erase ty) (erase tm)
erase (App tm1 args) = App (erase tm1) (erase <$> args)
erase (Let ty tm1 tm2) = Let (erase ty) (erase tm1) (erase tm2)
erase (Constr ind i args) =
  Constr (dummyInd ind) i (erase <$> args)
erase (Elim ind) = Elim (dummyInd ind)
erase t = t

precompElim :: Ind STy → Ind STy → [STm] → Int → [STm] → [STm]
precompElim cind eind eargs i cargs =
  concat $ zipWith aux (zip cargs' [0..]) (csArgs $ indConstructors cind !! i)
  where
    eargs' = take (indParamLength eind + 1 + length (indConstructors eind)) eargs
    cargs' = drop (indArgLength cind) cargs
    aux (ca, k) csa =
      if argRec csa
      then
        let absTys = argArgs csa in
        let absLen = length absTys in
        let vars = Var <$> reverse [0..absLen - 1] in
        let res = whnf (ESubst (Subst (reverse $ take k cargs) Map.empty) (argRes csa)) in
        let indices =
              if indIndicesLength cind <= 0
              then []
              else
                case res of
                  App _ indices -> drop (indParamLength cind) indices
                  _ -> error "Didn't reduce to an application of inductive type to parameters and indices"
        in
        let body = App (Elim eind) (eargs' ++ indices ++ [App ca vars]) in
            [ca, foldr Abs body absTys]
      else [ca]
      
whnf :: STm → STm
whnf s@(ESubst _ _) = whnf (pushSubst s)
whnf (App l []) = whnf l
whnf (App l r@(hr:tr)) = 
  case whnf l of
    Abs _ tm -> whnf (App (ESubst (Subst [hr] Map.empty) tm) tr)
    App l' r' -> whnf (App l' (r' ++ r)) 
    Constr ind i args -> let len = csFullArgsLength ind i in
                         if length r >= len then
                           App (Constr ind i args) r
                         else
                           let args' = take (len - length args) r in
                           let rest = drop (len - length args) r in
                             whnf (App (Constr ind i (args ++ args')) rest)
    Elim ind -> let len = elimArgLength ind in
                  if length r >= len
                  then
                    let args = take (len - 1) r in
                    let indices = drop (indParamLength ind + 1 + length (indConstructors ind)) args in
                    let cst = whnf (r !! (len - 1)) in
                    let rest = drop len r in
                      case cst of
                        Constr ind' i cargs ->
                          let pat = args !! (indParamLength ind + 1 + i) in
                          let cargs' = precompElim ind' ind args i cargs in
                            whnf (App pat (indices ++ cargs' ++ rest))
                        cst' -> App (Elim ind) (args ++ cst':rest)
                  else App (Elim ind) r
                   
    l' -> App l' r
whnf (Let _ tm1 tm2) = whnf (ESubst (Subst [tm2] Map.empty) tm1)
whnf t = t

conv :: STm -> STm -> Bool
conv tm tm' = aux (whnf tm) (whnf tm')
  where
    aux (Var i) (Var j) = i == j
    aux (U l) (U l') = l == l'
    aux (Ident s) (Ident s') = s == s'
    aux (Pi ty fam) (Pi ty' fam') = conv ty ty' && conv fam fam'
    aux (Abs ty tm) (Abs ty' tm') = conv ty ty' && conv tm tm'
    aux (App tm args) (App tm' args') = conv tm tm' && length args == length args' && (all (uncurry conv) $ zip args args')
    aux (Constr ind i args) (Constr ind' j args') = indName ind == indName ind' && i == j &&
                                                    length args == length args' && (all (uncurry conv) $ zip args args')
    aux (Elim ind) (Elim ind') = indName ind == indName ind'
    {- The ESubst and Let cases are always eliminated by whnf -}
    aux _ _ = False

z :: Constructor STy
z = Constructor "O" [] (Ident "nat")

sucArg :: CsArg STy
sucArg = CsArg [] (Ident "nat") True 

suc :: Constructor STy
suc = Constructor "S" [sucArg] (Ident "nat")

natAr :: Arity STy
natAr = Arity [] (Type 0)

nat :: Ind STy
nat = Ind "nat" [] natAr [z, suc]

sc :: STm
sc = Abs (Ident "nat") (Constr nat 1 [Var 0])

zero :: STm
zero = Constr nat 0 []

one :: STm
one = App sc [zero]

two :: STm
two = App sc [one]

double :: STm
double = App (Elim nat) [Abs (Ident "nat") (Ident "nat")
                        ,Constr nat 0 []
                        ,Abs (Ident "nat")
                          (Abs (Ident "nat")
                            (Constr nat 1
                             [Constr nat 1 [Var 0]])
                          )
                        ]
