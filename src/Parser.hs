{-# LANGUAGE UnicodeSyntax #-}

module Parser (module Parser) where

import Control.Applicative
import Control.Monad (foldM, void)
import Data.Char (ord)
import Syntax
import Term

newtype Parser a b = Parser { runParser :: a → Maybe (b, a) }

instance Functor (Parser a) where
  fmap f m = Parser (fmap (\ (b, as) → (f b, as)) . runParser m)
             
instance Applicative (Parser a) where
  mf <*> mx = Parser (\ as → runParser mf as >>= \ (f, as') →
                             runParser mx as' >>= \ (x, as'') →
                               pure (f x, as''))
  pure x = Parser (\ as → pure (x, as))

instance Alternative (Parser a) where
  empty = Parser (\ _ → Nothing)
  mx <|> my = Parser (\ as → runParser mx as <|> runParser my as)

instance Monad (Parser a) where
  m >>= f = Parser (\ as → runParser m as >>= \ (x, as') →
                           runParser (f x) as')

( << ) :: Monad m => m a → m b → m a
ma << mb =
  do
    a ← ma
    void mb
    pure a

data Stream a = Stream { streamData :: [a], streamRow :: Int, streamCol :: Int }
  deriving (Eq, Show)

data Loc a = Loc { locData :: a, locRow :: Int, locCol :: Int }
  deriving (Eq, Show)

data Pos = Pos { posRow :: Int, posCol :: Int }
  deriving (Eq, Show)

data Scoped a = Scoped { scopedData :: [a], scopes :: [Pos] }
  deriving (Eq, Show)

( @: ) :: a → Pos → Loc a
x @: p = Loc x (posRow p) (posCol p)

pos :: Loc a → Pos
pos x = Pos (locRow x) (locCol x)

( @< ) :: a → Loc b → Loc a
x @< y = x @: pos y

parserFail :: Parser a b
parserFail = Parser (const Nothing)

getStream :: Parser a a
getStream = Parser (\ s → Just (s,s))

setStream :: a → Parser a ()
setStream s = Parser (\ _ → Just ((),s))


parseMaybe :: Parser a b → Parser a (Maybe b)
parseMaybe p = Parser (\ s →
                         case runParser p s of
                           Nothing → Just (Nothing, s)
                           Just (res, s') → Just (Just res, s')
                      )

data Token
  = DefTok
  | IndTok
  | AxiomTok
  | CheckTok
  | PrintTok
  | FailTok
  | ImportTok String
  | NFTok
  | HNFTok
  | WHNFTok
  | Lambda
  | PiTok
  | ArrowTok
  | LetTok
  | ElimTok
  | DefEq
  | In
  | LParen
  | RParen
  | LBracket
  | RBracket
  | FilePath String
  | Identifier String
  | Number Int
  | Comma
  | Colon
  | Bar
  | Universe Int
  | PropTok
  deriving (Eq, Show)

nextCol :: Parser (Stream a) ()
nextCol =
  do
    str ← getStream
    setStream $ str { streamCol = 1 + streamCol str }

nextRow :: Parser (Stream a) ()
nextRow =
   do
    str ← getStream
    setStream $ str { streamCol = 0, streamRow = 1 + streamRow str }

getStreamData :: Parser (Stream a) [a]
getStreamData =
  do
    str ← getStream
    pure $ streamData str

setStreamData :: [a] → Parser (Stream a) ()
setStreamData cs =
  do
    str ← getStream
    setStream $ str { streamData = cs }

next :: Parser (Stream Char) Char
next =
  do
    cs ← getStreamData
    case cs of
      [] → parserFail
      (c:cs') → (if c == '\n' then nextRow else nextCol) >> setStreamData cs' >> pure c

char :: Char → Parser (Stream Char) Char
char c =
  do
    k ← next
    if k == c
      then pure c
      else parserFail

getCol :: Parser (Stream a) Int
getCol =
  do
    str ← getStream
    pure $ streamCol str

getRow :: Parser (Stream a) Int
getRow =
  do
    str ← getStream
    pure $ streamRow str

getPos :: Parser (Stream a) Pos
getPos =
  do
    col ← getCol
    row ← getRow
    pure (Pos row col)

setPos :: Pos → Parser (Stream a) ()
setPos p =
  do
    str ← getStream
    setStream $ str { streamRow = posRow p, streamCol = posCol p }
  
peeking :: Parser a b → Parser a b
peeking p =
  Parser
  (\ s →
     do
       (res, _) ← runParser p s
       pure (res, s)
  )

notFollowed :: Parser a b → Parser a c → Parser a b
notFollowed p f =
  do
    res ← p
    nxt ← parseMaybe $ peeking f
    case nxt of
      Just _ → parserFail
      Nothing → pure res

string :: String → Parser (Stream Char) String
string s = foldM (const $ void . char) () s >> pure s

oneOf :: [Parser a b] → Parser a b
oneOf = foldl ( <|> ) parserFail

alpha :: Parser (Stream Char) Char
alpha = oneOf $ char <$> "_abcdefghijklmnopqrtsuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

num :: Parser (Stream Char) Char
num = oneOf $ char <$> "0123456789"

index :: Parser (Stream Char) Char
index = oneOf $ char <$> "₀₁₂₃₄₅₆₇₈₉"

readDigit :: Char → Parser a Int
readDigit c =
  if (ord '0' <= ord c) && ord c <= ord '9'
  then pure (ord c - ord '0')
  else parserFail

readIndexDigit :: Char → Parser a Int
readIndexDigit c =
  if (ord '₀' <= ord c) && ord c <= ord '₉'
  then pure (ord c - ord '₀')
  else parserFail

digit :: Parser (Stream Char) Int
digit =
  do
    c ← num
    readDigit c

indexDigit :: Parser (Stream Char) Int
indexDigit =
  do
    c ← index
    readIndexDigit c

alphaNum :: Parser (Stream Char) Char
alphaNum = alpha <|> num <|> index <|> char '-'

identifier :: Parser (Stream Char) Token
identifier =
  do
    c ← alpha
    rest ← many alphaNum
    pure $ Identifier $ c:rest

number :: Parser (Stream Char) Token
number =
  do
    d0 ← digit
    digits ← many digit
    if (d0 == 0) && (digits /= [])
      then parserFail
      else pure $ Number $ foldl (\ i d → i * 10 + d) d0 digits

universe :: Parser (Stream Char) Token
universe =
  do
    void $ char 'U'
    d0 ← indexDigit
    digits ← many indexDigit
    if (d0 == 0) && (digits /= [])
      then parserFail
      else pure $ Universe $ foldl (\ i d → i * 10 + d) d0 digits

prop :: Parser (Stream Char) Token
prop = notFollowed (string "Prop") alphaNum >> pure PropTok

comma :: Parser (Stream Char) Token
comma = char ',' >> pure Comma

colon :: Parser (Stream Char) Token
colon = char ':' >> pure Colon

lbracket :: Parser (Stream Char) Token
lbracket = char '[' >> pure LBracket

rbracket :: Parser (Stream Char) Token
rbracket = char ']' >> pure RBracket

bar :: Parser (Stream Char) Token
bar = char '|' >> pure Bar

lambda :: Parser (Stream Char) Token
lambda = notFollowed (string "λ" <|> string "fun") alphaNum >> pure Lambda

piTok :: Parser (Stream Char) Token
piTok = notFollowed (string "Π" <|> string "Pi") alphaNum >> pure PiTok

arrowTok :: Parser (Stream Char) Token
arrowTok = notFollowed (string "→" <|> string "->") alphaNum >> pure ArrowTok

letTok :: Parser (Stream Char) Token
letTok = notFollowed (string "let") alphaNum >> pure LetTok

defEq :: Parser (Stream Char) Token
defEq = notFollowed (string ":=") alphaNum >> pure DefEq

inTok :: Parser (Stream Char) Token
inTok = notFollowed (string "in") alphaNum >> pure In

elimTok :: Parser (Stream Char) Token
elimTok = notFollowed (string "elim") alphaNum >> pure ElimTok

defTok :: Parser (Stream Char) Token
defTok = notFollowed (string "def") alphaNum >> pure DefTok

indTok :: Parser (Stream Char) Token
indTok = notFollowed (string "ind") alphaNum >> pure IndTok

axTok :: Parser (Stream Char) Token
axTok = notFollowed (string "axiom") alphaNum >> pure AxiomTok

checkTok :: Parser (Stream Char) Token
checkTok = notFollowed (string "#check") alphaNum >> pure CheckTok

printTok :: Parser (Stream Char) Token
printTok = notFollowed (string "#print") alphaNum >> pure PrintTok

failTok :: Parser (Stream Char) Token
failTok = notFollowed (string "#fail") alphaNum >> pure FailTok

munchLine :: Parser (Stream Char) ()
munchLine =
  do
    mc ← parseMaybe next
    case mc of
      Nothing → pure ()
      Just c → 
        if c == '\n'
        then pure ()
        else munchLine

comment :: Parser (Stream Char) ()
comment =
  do
    void $ string "--"
    munchLine

importTok :: Parser (Stream Char) Token
importTok =
  do
    void $ notFollowed (string "#import") alphaNum
    void $ hwhitespace
    beg ← some alphaNum
    rest ← many (alphaNum <|> char '/' <|> char '.')
    pure $ ImportTok $ beg ++ rest

nfTok :: Parser (Stream Char) Token
nfTok = notFollowed (string "#nf") alphaNum >> pure NFTok

hnfTok :: Parser (Stream Char) Token
hnfTok = notFollowed (string "#hnf") alphaNum >> pure HNFTok

whnfTok :: Parser (Stream Char) Token
whnfTok = notFollowed (string "#whnf") alphaNum >> pure WHNFTok

lparen :: Parser (Stream Char) Token
lparen = char '(' >> pure LParen

rparen :: Parser (Stream Char) Token
rparen = char ')' >> pure RParen

hwhitespace :: Parser (Stream Char) String
hwhitespace = many $ oneOf $ char <$> " \t\r"

whitespace :: Parser (Stream Char) String
whitespace = many $ oneOf $ char <$> " \t\r\n"

ignored :: Parser (Stream Char) ()
ignored = void $ many $ (void comment) <|> void (oneOf $ char <$> " \t\r\n")

token :: Parser (Stream Char) Token
token = oneOf
        [ lambda
        , piTok
        , arrowTok
        , defTok
        , indTok
        , axTok
        , checkTok
        , printTok
        , failTok
        , importTok
        , nfTok
        , hnfTok
        , whnfTok
        , lparen
        , rparen
        , lbracket
        , rbracket
        , universe
        , prop
        , number
        , comma
        , bar
        , letTok
        , defEq
        , colon
        , inTok
        , elimTok
        , identifier
        ]

tokenPos :: Parser (Stream Char) (Loc Token)
tokenPos =
  do
    p ← getPos
    tok ← token
    pure $ tok @: p

lexer :: Parser (Stream Char) [Loc Token]
lexer = ignored >> many (tokenPos << ignored)

anchor :: Pos → Parser (Scoped (Loc a)) ()
anchor p =
  do
    scope ← getStream
    setStream $ scope { scopes = p:scopes scope }

deanchor :: Parser (Scoped (Loc a)) ()
deanchor = 
  do
    scope ← getStream
    setStream $ scope { scopes = drop 1 $ scopes scope }

inScope :: Pos → Pos → Bool
inScope p scope = (posRow scope == posRow p) ||
                    (posRow scope <= posRow p
                     && posCol scope <= posCol p)

nextTok :: Parser (Scoped (Loc Token)) (Loc Token)
nextTok =
  do
    scope ← getStream
    case (scopedData scope, scopes scope) of
      ([], _) → parserFail
      ((t:ts), []) → setStream (scope { scopedData = ts }) >> pure t
      ((t:ts), p:_) → 
        if pos t `inScope` p
        then setStream (scope { scopedData = ts }) >> pure t
        else parserFail

parseTok :: Token → Parser (Scoped (Loc Token)) (Loc Token)
parseTok tok =
  do
    t ← nextTok
    if locData t == tok
      then pure t
      else parserFail

parseIdent :: Parser (Scoped (Loc Token)) (Loc String)
parseIdent =
  do
    tok ← nextTok
    case locData tok of
      Identifier s → pure $ (s @< tok)
      _ → parserFail

parseIdentStrict :: Parser (Scoped (Loc Token)) (Loc String)
parseIdentStrict =
  do
    tok ← nextTok
    case locData tok of
      Identifier "_" → parserFail
      Identifier s → pure $ (s @< tok)
      _ → parserFail

parseLvl :: Parser (Scoped (Loc Token)) (Loc Lvl)
parseLvl =
  do
    tok ← nextTok
    case locData tok of
      Universe i → pure $ (Type i) @< tok
      PropTok → pure $ Prop @< tok
      _ → parserFail

univ :: Parser (Scoped (Loc Token)) (Loc PTm)
univ =
  do
     lvl ← parseLvl
     pure $ (PU (locData lvl)) @< lvl

ident :: Parser (Scoped (Loc Token)) (Loc PTm)
ident =
  do
    s ← parseIdentStrict
    pure $ (PIdent (locData s)) @< s

elim :: Parser (Scoped (Loc Token)) (Loc PTm)
elim =
  do
    s ← parseTok ElimTok
    lvl ← locData <$> parseLvl
    ind ← locData <$> parseIdent
    pure $ (PElim lvl ind) @< s

expr :: Parser (Scoped (Loc (Token))) (Loc PTm)
expr =
  (do
    ty ← expr'
    anchor $ pos ty
    void $ parseTok ArrowTok
    fam ← locData <$> expr
    deanchor
    pure $ (PPi "_" (locData ty) fam) @< ty
 ) <|> expr' 

expr' :: Parser (Scoped (Loc (Token))) (Loc PTm)
expr' =
  do
    tm ← expr''
    args ← (fmap locData) <$> many expr''
    if args == []
    then pure tm
    else pure $ (PApp (locData tm) args) @< tm

expr'' :: Parser (Scoped (Loc Token)) (Loc PTm)
expr'' = oneOf
        [parseAbs
        , parsePi
        , univ
        , letExpr
        , cast
        , elim
        , parentExpr
        , ident]

parentExpr :: Parser (Scoped (Loc Token)) (Loc PTm)
parentExpr =
  do
    beg ← parseTok LParen
    anchor $ pos beg
    res ← locData <$> expr
    void $ parseTok RParen
    deanchor
    pure $ res @< beg

varDecl :: Parser (Scoped (Loc Token)) (Loc (String, PTy))
varDecl =
  do
    beg ← parseTok LParen
    anchor $ pos beg
    var ← locData <$> parseIdent
    void $ parseTok Colon
    ty ← locData <$> expr
    void $ parseTok RParen
    deanchor
    pure $ (var, ty) @< beg

cast :: Parser (Scoped (Loc Token)) (Loc PTm)
cast =
  do
    beg ← parseTok LParen
    anchor $ pos beg
    tm ← locData <$> expr
    void $ parseTok Colon
    ty ← locData <$> expr
    void $ parseTok RParen
    deanchor
    pure $ (PCast tm ty) @< beg

parseAbs :: Parser (Scoped (Loc Token)) (Loc PTm)
parseAbs =
  do
    beg ← parseTok Lambda
    anchor $ pos beg
    (name, ty) ← locData <$> varDecl
    void $ parseTok Comma
    body ← locData <$> expr
    deanchor
    pure $ (PAbs name ty body) @< beg

parsePi :: Parser (Scoped (Loc Token)) (Loc PTm)
parsePi =
  do
    beg ← parseTok PiTok
    anchor $ pos beg
    (name, ty) ← locData <$> varDecl
    fam ← locData <$> expr
    deanchor
    pure $ (PPi name ty fam) @< beg

letExpr :: Parser (Scoped (Loc Token)) (Loc PTm)
letExpr =
  do
    beg ← parseTok LetTok
    anchor $ pos beg
    (name, ty) ← locData <$> varDecl
    defeq ← parseTok DefEq
    anchor $ pos defeq
    tm1 ← locData <$> expr
    deanchor
    tokIn ← parseTok In
    anchor $ pos tokIn
    tm2 ← locData <$> expr
    deanchor
    deanchor
    pure $ (PLet name ty tm1 tm2) @< beg

definition :: Parser (Scoped (Loc Token)) (Loc Command)
definition =
  do
    beg ← parseTok DefTok
    anchor $ pos beg
    name ← locData <$> parseIdent
    ty ← (fmap locData) <$> (parseMaybe $ parseTok Colon >> expr)
    defeq ← parseTok DefEq
    anchor $ pos defeq
    body ← locData <$> expr
    deanchor
    deanchor
    pure $ (Definition $ DefCmd name ty body) @< beg

constructor :: Parser (Scoped (Loc Token)) (Loc (String, PTy))
constructor =
  do
    beg ← parseTok Bar
    anchor $ pos beg
    name ← locData <$> parseIdent
    void $ parseTok Colon
    ty ← locData <$> expr
    deanchor
    pure $ (name, ty) @< beg

inductive :: Parser (Scoped (Loc Token)) (Loc Command)
inductive =
  do
    beg ← parseTok IndTok
    anchor $ pos beg
    name ← locData <$> parseIdent
    params ← (fmap locData) <$> many varDecl
    void $ parseTok Colon
    ar ← locData <$> expr
    constr ← (fmap locData) <$> many constructor
    deanchor
    deanchor
    pure $ (Inductive $ PreInd name params ar constr) @< beg

axiom :: Parser (Scoped (Loc Token)) (Loc Command)
axiom =
  do
    beg ← parseTok AxiomTok
    anchor $ pos beg
    name ← locData <$> parseIdent
    ty ← locData <$> (parseTok Colon >> expr)
    deanchor
    pure $ (Axiom name ty) @< beg

checkCmd :: Parser (Scoped (Loc Token)) (Loc Command)
checkCmd =
  do
    beg ← parseTok CheckTok
    anchor $ pos beg
    tm ← locData <$> expr
    deanchor
    pure $ (Check tm) @< beg

printCmd :: Parser (Scoped (Loc Token)) (Loc Command)
printCmd =
  do
    beg ← parseTok PrintTok
    anchor $ pos beg
    name ← locData <$> parseIdent
    deanchor
    pure $ (Print name) @< beg

failCmd :: Parser (Scoped (Loc Token)) (Loc Command)
failCmd =
  do
    beg ← parseTok FailTok
    anchor $ pos beg
    cmd ← locData <$> command
    deanchor
    pure $ (Fail cmd) @< beg

importCmd :: Parser (Scoped (Loc Token)) (Loc Command)
importCmd =
  do
    tok ← nextTok
    case locData tok of
      ImportTok s → pure $ (Import s) @< tok
      _ → parserFail

nfCmd :: Parser (Scoped (Loc Token)) (Loc Command)
nfCmd =
  do
    beg ← parseTok NFTok
    anchor $ pos beg
    tm ← locData <$> expr
    deanchor
    pure $ (NF tm) @< beg

hnfCmd :: Parser (Scoped (Loc Token)) (Loc Command)
hnfCmd =
  do
    beg ← parseTok HNFTok
    anchor $ pos beg
    tm ← locData <$> expr
    deanchor
    pure $ (HNF tm) @< beg

whnfCmd :: Parser (Scoped (Loc Token)) (Loc Command)
whnfCmd =
  do
    beg ← parseTok WHNFTok
    anchor $ pos beg
    tm ← locData <$> expr
    deanchor
    pure $ (WHNF tm) @< beg

command :: Parser (Scoped (Loc Token)) (Loc Command)
command = oneOf
          [ definition
          , inductive
          , axiom
          , checkCmd
          , printCmd
          , importCmd
          , failCmd
          , nfCmd
          , hnfCmd
          , whnfCmd
          ]

script :: Parser (Scoped (Loc Token)) [Loc Command]
script = many command
