{-# LANGUAGE UnicodeSyntax #-}

module WHNF (module WHNF) where

import Name
import Ind
import Term
import Ctx

{-
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

nTimes :: Int -> (a -> a) -> a -> a
nTimes 0 _ x = x
nTimes n f x = f (nTimes (n - 1) f x)

data SubstV
  = Empty
  | Shift Int
  | Bind STm SubstV
  | Comp SubstV SubstV
  deriving Eq

 data Subst = Subst { vars :: SubstV, idents :: Map.Map String STm }
  deriving Eq

data STm
  = Var Int
  | U Lvl
  | Pi STy STy
  | Abs STy STm
  | App STm [STm]
  | Let STy STm STm
  | Ident String
  | Cast STm STy
  | Constr (Ind STy) Int
  | Elim Lvl (Ind STy)
  | ESubst Subst STm
  deriving Eq

type STy = STm

instance Show SubstV where
  show Empty = "ι"
  show (Shift n) = "↑{"++ show n ++ "}"
  show (Bind tm s) = show tm ++ "∙" ++ show s
  show (Comp s s') = "(" ++ show s ++ ") ∘ (" ++ show s' ++ ")"

instance Show Subst where
  show s = show (vars s) ++ " | " ++ (intercalate ";" ((\ (i, tm) -> show i ++ " := " ++ show tm) <$> (Map.toList $ idents s)))

instance Show STm where
  show (Var i) = "x" ++ show i
  show (U lvl) = show lvl
  show (Pi ty1 ty2) = "Π[" ++ show ty1 ++ "]." ++ show ty2
  show (Abs ty tm) = "λ[" ++ show ty ++ "]." ++ show tm
  show (Let ty tm1 tm2) = "let[" ++ show ty ++ "] := " ++ show tm1 ++ " in " ++ show tm2
  show (Ident s) = s
  show (Cast tm ty) = "(" ++ show tm ++ " : " ++ show ty ++ ")"
  show (Constr ind i) =
    let dummy = "cs{" ++ indName ind ++ "; " ++ show i ++ "}"  in
      fromMaybe dummy (csName <$> (indConstructors ind `atMay` i))
  show (Elim lvl ind) = "elim{" ++ indName ind ++ " ▸ " ++ show lvl ++ "}"
  show (ESubst s tm) = "(" ++ show tm ++ ")[" ++ show s ++ "]"
  show (App tm args) = show tm ++ " " ++ (intercalate " " $ bracketArg <$> args)
    where
      bracketArg :: STm -> String
      bracketArg tm@(Abs _ _) = "(" ++ show tm ++ ")"
      bracketArg tm@(App _ _) = "(" ++ show tm ++ ")"
      bracketArg tm@(Let _ _ _) = "(" ++ show tm ++ ")"
      bracketArg tm = show tm

substVar :: SubstV -> Int -> STm
substVar Empty i = Var i
substVar (Shift n) i = Var (i + n)
substVar (Bind tm s) 0 = tm
substVar (Bind tm s) i = substVar s (i - 1)
substVar (Comp s s') i = ESubst (Subst s' Map.empty) (substVar s i)

substFromList :: [STm] -> SubstV
substFromList = foldr Bind Empty

substSingleton :: STm -> SubstV
substSingleton tm = Bind tm Empty

bump :: Int → Int → STm → STm
bump n k tm =
  ESubst
  (Subst
   (foldr (Bind . Var)
    (Shift k)
    [0..n-1]
   )
   Map.empty)
  tm

lift :: Subst → Subst
lift s = s { vars = Bind (Var 0) (Comp (vars s) (Shift 1)) }

composeSubst :: Subst → Subst → Subst
composeSubst outer inner = Subst (Comp (vars inner) (vars outer)) (idents inner `Map.union` idents outer)

pushSubst :: STm → STm
pushSubst (ESubst sb t) = aux sb t
  where
    aux s (ESubst s' t') = aux (composeSubst s s') t'
    aux s (Var i) = pushSubst (substVar (vars s) i)
    aux _ (U l) = U l
    aux s (Pi ty tm) = Pi (ESubst s ty) (ESubst (lift s) tm)
    aux s (Abs ty tm) = Abs (ESubst s ty) (ESubst (lift s) tm)
    aux s (App tm1 args) = App (ESubst s tm1) (ESubst s <$> args)
    aux s (Let ty tm1 tm2) = Let (ESubst s ty) (ESubst (lift s) tm1) (ESubst (lift s) tm2)
    aux s (Ident i) = fromMaybe (Ident i) (idents s Map.!? i)
    aux s (Cast tm ty) = Cast (ESubst s tm) (ESubst s ty)
    aux _ (Constr ind i) = Constr ind i
    aux _ (Elim lvl ind) = Elim lvl ind
pushSubst t = t

execSubst :: STm → STm
execSubst t = aux (Subst Empty Map.empty) t
  where
    aux s (ESubst s' t') = aux (composeSubst s s') t'
    aux s (Var i) = execSubst (substVar (vars s) i)
    aux _ (U l) = U l
    aux s (Pi ty tm) = Pi (aux s ty) (aux (lift s) tm)
    aux s (Abs ty tm) = Abs (aux s ty) (aux (lift s) tm)
    aux s (App tm1 args) = App (aux s tm1) (aux s <$> args)
    aux s (Let ty tm1 tm2) = Let (aux s ty) (aux s tm1) (aux (lift s) tm2)
    aux s (Ident i) = fromMaybe (Ident i) (idents s Map.!? i)
    aux s (Cast tm ty) = Cast (aux s tm) (aux s ty)
    aux _ (Constr ind i) = Constr ind i
    aux _ (Elim lvl ind) = Elim lvl ind

dummyInd :: Ind STy -> Ind STy
dummyInd ind = Ind (indName ind) [] (Arity [] Prop) []

erase :: STm -> STm
erase (Pi ty tm) = Pi (erase ty) (erase tm)
erase (Abs ty tm) = Abs (erase ty) (erase tm)
erase (App tm1 args) = App (erase tm1) (erase <$> args)
erase (Let ty tm1 tm2) = Let (erase ty) (erase tm1) (erase tm2)
erase (Cast tm ty) = Cast (erase tm) (erase ty)
erase (Constr ind i) = Constr (dummyInd ind) i 
erase (Elim lvl ind) = Elim lvl (dummyInd ind)
erase t = t

clean :: STm -> STm
clean (Pi ty tm) = Pi (clean ty) (clean tm)
clean (Abs ty tm) = Abs (clean ty) (clean tm)
clean (App tm1 []) = clean tm1
clean (App (App tm args1) args2) = clean (App tm (args1 ++ args2))
clean (App tm1 args) = App (clean tm1) (clean <$> args)
clean (Let ty tm1 tm2) = Let (clean ty) (clean tm1) (clean tm2)
clean (Cast tm ty) = Cast (clean tm) (clean ty)
clean (Constr ind i) = Constr ind i 
clean (Elim lvl ind) = Elim lvl ind
clean t = t

precompElim :: Lvl → Ind STy → Ind STy → [STm] → Int → [STm] → [STm]
precompElim lvl cind eind eargs i cargs =
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
        let res = whnf (ESubst (Subst (substFromList (reverse $ take k cargs)) Map.empty) (argRes csa)) in
        let indices =
              if indIndicesLength cind <= 0
              then []
              else
                case res of
                  App _ indices -> drop (indParamLength cind) indices
                  _ -> error "Didn't reduce to an application of inductive type to parameters and indices"
        in
        let body = App (Elim lvl eind) (eargs' ++ indices ++ [App ca vars]) in
            [ca, foldr Abs body absTys]
      else [ca]

-}

-- Pop at most 'depth' abstractions from a term
unravelAbs :: Int → Tm → ([(Name, Ty)], Tm)
unravelAbs 0 tm = ([], tm)
unravelAbs depth (Abs name ty tm) =
  let (names, tm') = unravelAbs (depth - 1) tm
  in ((name,ty):names, tm)
unravelAbs _ tm = ([], tm)

whnf :: Tm → InCtx Tm
whnf (App l []) = whnf l
whnf (App l r@(hr:tr)) =
  do
    l' ← whnf l
    case l' of
      Abs _ ty tm →
        let (names, tm) = unravelAbs (length r) l' in
        let args = take (length names) r in
        let rem = drop (length names) r in
          whnf (App (instantiate args tm) rem)
      App l' r' → whnf (App l' (r' ++ r)) 
      Elim lvl nameInd →
        do
          { ind ← getInd nameInd
          ; let len = elimArgLength ind
          ; if length r >= len
            then fail "Not yet implemented : Reduction of eliminators"
            else pure $ App (Elim lvl nameInd) r
          }
      Cast l' _ -> whnf (App l' r)               
      l' -> pure $ App l' r
whnf (Let _ _ tm1 tm2) = whnf (instantiate [tm1] tm2)
whnf (Cast tm ty) =
  do tm' ← whnf tm
     pure $ Cast tm' ty
whnf t = pure t
{-
hnf :: STm -> STm
hnf tm = aux (whnf tm)
  where
    aux (Pi ty fam) = Pi (hnf ty) (hnf fam)
    aux (Abs ty tm) = Abs (hnf ty) (hnf tm)
    aux (App tm args) = App (hnf tm) args
    aux (Cast tm ty) = Cast (hnf tm) (hnf ty)
    {- The ESubst and Let cases are always eliminated by whnf -}
    aux t = t

nf :: STm -> STm
nf tm = aux (whnf tm)
  where
    aux (Pi ty fam) = Pi (nf ty) (nf fam)
    aux (Abs ty tm) = Abs (nf ty) (nf tm)
    aux (App tm args) = App (nf tm) (nf <$> args)
    aux (Cast tm ty) = Cast (nf tm) (nf ty)
    {- The ESubst and Let cases are always eliminated by wnf -}
    aux t = t
    

conv :: STm -> STm -> Bool
conv tm tm' = aux (whnf tm) (whnf tm')
  where
    aux (Var i) (Var j) = i == j
    aux (U l) (U l') = l == l'
    aux (Ident s) (Ident s') = s == s'
    aux (Pi ty fam) (Pi ty' fam') = conv ty ty' && conv fam fam'
    aux (Abs _ tm) (Abs _ tm') = conv tm tm'
    aux (App tm args) (App tm' args') = conv tm tm' && length args == length args' && (all (uncurry conv) $ zip args args')
    aux (Cast tm ty) (Cast tm' ty') = conv tm tm'
    aux (Elim lvl ind) (Elim lvl' ind') = lvl == lvl' && indName ind == indName ind'
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
sc = Constr nat 1

addTwo :: STm
addTwo = Abs (Ident "nat") (App sc [App sc [Var 0]])

zero :: STm
zero = Constr nat 0

one :: STm
one = App sc [zero]

two :: STm
two = App sc [one]

double :: STm
double = App (Elim (Type 0) nat)
          [Abs (Ident "nat") (Ident "nat")
          ,zero
          ,Abs (Ident "nat")
            (Abs (Ident "nat")
              (App (Constr nat 1)
                [App (Constr nat 1) [Var 0]])
            )
          ]

nil :: Constructor STy
nil = Constructor "nil" [] (App (Ident "list") [Var 0])

consArg1 :: CsArg STy
consArg1 = CsArg [] (Var 0) False

consArg2 :: CsArg STy
consArg2 = CsArg [] (App (Ident "list") [Var 1]) True

cons :: Constructor STy
cons = Constructor "cons" [consArg1, consArg2] (App (Ident "list") [Var 2])

listAr :: Arity STy
listAr = Arity [] (Type 0)

list :: Ind STy
list = Ind "list" [U (Type 0)] natAr [nil, cons]

nilT :: STm
nilT = Constr list 0

consT :: STm
consT = Constr list 1

lengthTpre :: STm
lengthTpre = Abs (U (Type 0))
           (App (Elim (Type 0) list)
            [Var 0
            , Abs (App (Ident "list") [Var 0]) (Ident "nat")
            ])


lengthT :: STm
lengthT = Abs (U (Type 0))
           (App (Elim (Type 0) list)
            [Var 0
            , Abs (App (Ident "list") [Var 0]) (Ident "nat")
            , zero
            , Abs (Var 0)
              (Abs (App (Ident "list") [Var 1]) sc)
            ])

refl :: Constructor STy
refl = Constructor "refl" [] (App (Ident "eq") [Var 0, Var 0])

eqAr :: Arity STy
eqAr = Arity [Var 1] (Type 0)

eq :: Ind STy
eq = Ind "eq" [U (Type 0), Var 0] eqAr [refl]

-}
