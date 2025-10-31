
module Parser (parseString, parseStdin, parseStringProgram) where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import System.Exit
import Text.Megaparsec

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

import Common
import Presyntax
import Definition 
import Control.Exception (throwIO)
import Errors (TopLevelError(..))

--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

bar :: Parser ()
bar = void (char '|')

withPos :: Parser Tm -> Parser Tm
withPos p = SrcPos <$> getSourcePos <*> p

lexeme     = L.lexeme ws
symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
parens p   = char '(' *> p <* char ')'
braces p   = char '{' *> p <* char '}'
brackets p   = char '[' *> p <* char ']'
pArrow     = symbol "→" <|> symbol "->"
pBind      = pIdent <|> symbol "_"

keyword :: String -> Bool
keyword x = x == "let" || x == "λ" || x == "U" || x == "def" || x == "data" || x == "where" || x == "printcxt" || x == "sorry" || x == "mutual" || x == "begin" || x == "end"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pAtom :: Parser Tm
pAtom  =
      withPos (    (Var <$> pIdent)
               <|> (U <$ char 'U')
               <|> (Hole <$ char '_'))
  <|> parens pTm
  <|> (pKeyword "printcxt" >> brackets pTm >>= pure . PrintCxt)
  <|> (pKeyword "sorry" >> pure (PrintCxt Hole))

pArg :: Parser (Either Name Icit, Tm)
pArg =  (try $ braces $ do {x <- pIdent; char '='; t <- pTm; pure (Left x, t)})
    <|> ((Right Impl,) <$> (char '{' *> pTm <* char '}'))
    <|> ((Right Expl,) <$> pAtom)

pSpine :: Parser Tm
pSpine = do
  h <- pAtom
  args <- many pArg
  pure $ foldl (\t (i, u) -> App t u i) h args

pLamBinder :: Parser (Name, Either Name Icit)
pLamBinder =
      ((,Right Expl) <$> pBind)
  <|> try ((,Right Impl) <$> braces pBind)
  <|> braces (do {x <- pIdent; char '='; y <- pBind; pure (y, Left x)})

pLam :: Parser Tm
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pLamBinder
  char '.'
  t <- pTm
  pure $ foldr (uncurry Lam) t xs

pPiBinder :: Parser ([Name], Tm, Icit)
pPiBinder =
      braces ((,,Impl) <$> some pBind
                       <*> ((char ':' *> pTm) <|> pure Hole))
  <|> parens ((,,Expl) <$> some pBind
                       <*> (char ':' *> pTm))
pPi :: Parser Tm
pPi = do
  dom <- some pPiBinder
  pArrow
  cod <- pTm
  pure $ foldr (\(xs, a, i) t -> foldr (\x -> Pi x i a) t xs) cod dom

pFunOrSpine :: Parser Tm
pFunOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> Pi "_" Expl sp <$> pTm

pLet :: Parser Tm
pLet = do
  pKeyword "let"
  x <- pIdent
  ann <- optional (char ':' *> pTm)
  char '='
  t <- pTm
  symbol ";"
  u <- pTm
  pure $ Let x (maybe Hole id ann) t u

pTm :: Parser Tm
pTm = withPos (pLam <|> pLet <|> try pPi <|> pFunOrSpine)

pSrc :: Parser Tm
pSrc = ws *> pTm <* eof

parseString :: String -> IO Tm
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO (Tm, String)
parseStdin = do
  src <- getContents
  t <- parseString src
  pure (t, src)



{-
func_def ::= 
    `def` id `:` tm 
    clause

clause ::= 
  | `=` tm
  | `|` patterns = tm clause

pattern ::= id patterns

pattern' :: 
  | id
  | (pattern)
  | {pattern}
  | {id = pattern}

patterns ::= pattern'*
-}

pFunc :: Parser RFuncDef
pFunc = do
  pKeyword "def"
  f <- pIdent
  ann <- optional (char ':' *> pTm)
  cls <- many pClause
  pure $ RFuncDef f (maybe Hole id ann) cls

pPatterns :: Parser RPatterns
pPatterns = many pPattern'

pPattern' :: Parser (Either Name Icit, RPattern)
pPattern' =
      (pIdent >>= \x -> pure (Right Expl, RPat x []))
  <|> braces (
            try (pPattern >>= \p -> pure (Right Impl, p))
        <|> do 
              n <- pIdent
              p <- char ':' >> pPattern
              pure (Left n, p)
      )
  <|> parens (pPattern >>= \p -> pure (Right Expl, p))

pPattern :: Parser RPattern
pPattern = do 
  c <- pIdent
  args <- pPatterns
  pure (RPat c args)

pClause :: Parser RClause
pClause = 
      do 
        rhs <- char '=' >> pTm
        pure (RClause [] rhs)
  <|> do 
        ps <- bar >> pPatterns 
        rhs <- char '=' >> pTm 
        pure (RClause ps rhs)

{-

data_def ::= 
  `data` id `:` tm `where`
  `|` id `:` tm 
  ...
-}

pData :: Parser RDataDef
pData = do 
  name <- pKeyword "data" >> pIdent 
  ty <- optional (char ':' >> pTm) 
  optional (pKeyword "where")
  cls <- many pConstructor
  pure $ RDataDef name (maybe U id ty) cls

pConstructor :: Parser (Name, Tm)
pConstructor = do 
  n <- bar >> pIdent  
  ty <- char ':' >> pTm 
  pure (n, ty)

{-
mutual_block ::= 
  `mutual`
    mutual_sig
    ... 
  `begin`
    mutual_body
    ...
  `end`

mutual_sig ::=
  func_header | data_header
func_header ::=
  `def` id `:` tm
data_header ::=
  `data` id `:` tm

mutual_body ::=
  func_body | data_body
func_body ::=
  `def` id 
    clause
    ...
data_body ::=
  `data` id 
    `|` id `:` tm
    ...
-}

pMutualBlock :: Parser RMutalBlock
pMutualBlock = do
  pKeyword "mutual"
  sigs <- many pMutualSig
  pKeyword "begin"
  bodys <- many pMutualBody
  pKeyword "end"
  pure $ RMutalBlock sigs bodys

pMutualSig :: Parser (SourcePos, Header)
pMutualSig = do 
  spos <- getSourcePos
  header <- (pKeyword "def" >> do 
                name <- pIdent
                ty <- char ':' >> pTm
                pure $ FunHeader name ty)
            <|> (pKeyword "data" >> do 
                name <- pIdent
                ty <- char ':' >> pTm
                pure $ DataHeader name ty)
  pure (spos, header)

pMutualBody :: Parser (SourcePos, Body)
pMutualBody = do
  spos <- getSourcePos
  body <- (pKeyword "def" >> do 
              name <- pIdent
              cls <- many pClause
              pure $ FunBody name cls)
          <|> (pKeyword "data" >> do 
              name <- pIdent
              cls <- many pConstructor
              pure $ DataBody name cls)
  pure (spos, body)


pDef :: Parser (SourcePos, RDef)
pDef = do 
  spos <- getSourcePos
  def <- (pFunc >>= pure . RDefFunc) <|> (pData >>= pure . RDefData) <|> (pMutualBlock >>= pure . RDefMutual)
  pure (spos, def)

pProgram :: Parser Program 
pProgram = many pDef

parseStringProgram :: String -> String -> IO Program
parseStringProgram fp src = 
    case parse (ws >> pProgram <* eof) fp src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      throwIO TopLevelError
    Right t ->
      pure t



