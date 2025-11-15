{-# LANGUAGE UnicodeSyntax #-}

module Parser (module Parser) where

import Control.Applicative
import Control.Monad (foldM, void)
import Data.Char (ord)

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
    mb
    pure a

data Stream a = Stream { streamData :: [a], streamRow :: Int, streamCol :: Int }
  deriving (Eq, Show)

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
  = Definition
  | Inductive
  | Lambda
  | TokPi
  | Let
  | DefEq
  | In
  | LParen
  | RParen
  | LBracket
  | RBracket
  | Identifier String
  | Number Int
  | Comma
  | Colon
  | Bar
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
      (c:cs) → (if c == '\n' then nextRow else nextCol) >> setStreamData cs >> pure c

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

getPos :: Parser (Stream a) (Int, Int)
getPos =
  do
    col ← getCol
    row ← getRow
    pure (row, col)

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
    next ← parseMaybe $ peeking f
    case next of
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

readDigit :: Char → Parser a Int
readDigit c =
  if (ord '0' <= ord c) && ord c <= ord '9'
  then pure (ord c - ord '0')
  else parserFail

digit :: Parser (Stream Char) Int
digit =
  do
    c ← num
    readDigit c

alphaNum :: Parser (Stream Char) Char
alphaNum = alpha <|> num

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
    pure $ Number $ foldl (\ i d → i * 10 + d) d0 digits
                    
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
piTok = notFollowed (string "Π" <|> string "Pi") alphaNum >> pure TokPi

letTok :: Parser (Stream Char) Token
letTok = notFollowed (string "let") alphaNum >> pure Let

defEq :: Parser (Stream Char) Token
defEq = notFollowed (string ":=") alphaNum >> pure DefEq

inTok :: Parser (Stream Char) Token
inTok = notFollowed (string "in") alphaNum >> pure In

definition :: Parser (Stream Char) Token
definition = notFollowed (string "def") alphaNum >> pure Definition

inductive :: Parser (Stream Char) Token
inductive = notFollowed (string "ind") alphaNum >> pure Inductive

lparen :: Parser (Stream Char) Token
lparen = char '(' >> pure LParen

rparen :: Parser (Stream Char) Token
rparen = char ')' >> pure LParen

whitespace :: Parser (Stream Char) String
whitespace = many $ oneOf $ char <$> " \t\r\n"

token :: Parser (Stream Char) Token
token = oneOf
        [ lambda
        , piTok
        , definition
        , inductive
        , lparen
        , rparen
        , lbracket
        , rbracket
        , number
        , comma
        , bar
        , letTok
        , defEq
        , colon
        , inTok
        , identifier]

tokenPos :: Parser (Stream Char) (Token, (Int, Int))
tokenPos =
  do
    pos ← getPos
    tok ← token
    pure (tok, pos)

lexer :: Parser (Stream Char) [(Token, (Int, Int))]
lexer = many (tokenPos << whitespace)
