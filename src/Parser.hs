{-# LANGUAGE UnicodeSyntax #-}

module Parser (module Parser) where

import Control.Applicative
import Control.Monad (foldM, void)
import Data.Char (ord)

newtype Parser a b = Parser { runParser :: [a] → Maybe (b, [a]) }

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

parserFail :: Parser a b
parserFail = Parser (const Nothing)

getStream :: Parser a [a]
getStream = Parser (\ s → Just (s,s))

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
  | In
  | LParen
  | RParen
  | Identifier String
  | Number Int
  | Comma
  | Colon
  | LBracket
  | RBracket
  | Bar
  deriving (Eq, Show)

char :: Char → Parser Char Char
char c = Parser aux
  where
    aux [] = Nothing
    aux (k:ks) =
      if c == k
      then pure (c, ks)
      else Nothing

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

string :: String → Parser Char String
string s = foldM (const $ void . char) () s >> pure s

oneOf :: [Parser a b] → Parser a b
oneOf = foldl ( <|> ) parserFail

alpha :: Parser Char Char
alpha = oneOf $ char <$> "_abcdefghijklmnopqrtsuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

num :: Parser Char Char
num = oneOf $ char <$> "0123456789"

readDigit :: Char → Parser a Int
readDigit c =
  if (ord '0' <= ord c) && ord c <= ord '9'
  then pure (ord c - ord '0')
  else parserFail

digit :: Parser Char Int
digit =
  do
    c ← num
    readDigit c

alphaNum :: Parser Char Char
alphaNum = alpha <|> num

identifier :: Parser Char Token
identifier =
  do
    c ← alpha
    rest ← many alphaNum
    pure $ Identifier $ c:rest

number :: Parser Char Token
number =
  do
    d0 ← digit
    digits ← many digit
    pure $ Number $ foldl (\ i d → i * 10 + d) d0 digits
                    
comma :: Parser Char Token
comma = char ',' >> pure Comma

colon :: Parser Char Token
colon = char ':' >> pure Colon

lbracket :: Parser Char Token
lbracket = char '[' >> pure LBracket

rbracket :: Parser Char Token
rbracket = char ']' >> pure RBracket

bar :: Parser Char Token
bar = char '|' >> pure Bar

lambda :: Parser Char Token
lambda = notFollowed (string "λ" <|> string "fun") alphaNum >> pure Lambda

piTok :: Parser Char Token
piTok = notFollowed (string "Π" <|> string "Pi") alphaNum >> pure TokPi

letTok :: Parser Char Token
letTok = notFollowed (string "let") alphaNum >> pure Let

inTok :: Parser Char Token
inTok = notFollowed (string "in") alphaNum >> pure In

definition :: Parser Char Token
definition = notFollowed (string "def") alphaNum >> pure Definition

inductive :: Parser Char Token
inductive = notFollowed (string "ind") alphaNum >> pure Inductive

lparen :: Parser Char Token
lparen = char '(' >> pure LParen

rparen :: Parser Char Token
rparen = char ')' >> pure LParen

whitespace :: Parser Char String
whitespace = many $ oneOf $ char <$> " \t\r"

indent :: Parser Char Int
indent =
  do
    pre ← many $ char ' '
    pure $ length pre

token :: Parser Char Token
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
        , colon
        , bar
        , letTok
        , inTok
        , identifier]

offset :: Parser a b → Parser a (b, Int)
offset p =
  do
    len0 ← length <$> getStream
    res ← p
    len1 ← length <$> getStream
    pure (res, len0 - len1)

lexerLine :: Parser Char ([(Token, Int)])
lexerLine = rep 0 << whitespace
  where
    rep i =
      do
        w ← length <$> whitespace
        res ← parseMaybe (offset token)
        case res of
          Nothing → pure []
          Just (tok, j) →
            do
              { rest ← rep (i + w + j)
              ; pure $ (tok, i + w):rest
              }
  
lexer :: Parser Char [[(Token, Int)]]
lexer =
  do
    lns ← many (lexerLine << char '\n')
    final ← lexerLine
    pure (lns ++ [final])
    
