{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <&>" #-}
{-# HLINT ignore "Use <$>" #-}
{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, decl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang hiding (getPos)
import Common
import Text.Parsec hiding (runP,parse)
--import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "rec","fun", "fix", "then", "else","in",
                           "ifz", "print","Nat","type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

tyIdentifier :: P String
tyIdentifier = Tok.lexeme lexer $ do
  c  <- upper
  cs <- many (identLetter langDef)
  return (c:cs)

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P SType
tyatom = (reserved "Nat" >> return SNatTy)
         <|> parens typeP

tysvt :: P SType
tysvt = (SVT <$> tyIdentifier) <|> parens typeP

typeP' :: P SType
typeP' = try (do
          x <- tyatom <|> tysvt
          reservedOp "->"
          y <- typeP'
          return (SFunTy x y))
        <|> tyatom
        <|> tysvt

typeP :: P SType
typeP = try typeP' 

const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  a <- atom
  return (SPrint i str a)

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea un par (variable : tipo)
binding :: P (Name, SType)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v, ty)

multibinding :: P [(Name, SType)]
multibinding = do 
  vs <- many1 var 
  reservedOp ":"
  ty <- typeP
  return [(v, ty) | v <- vs]

-- multibind 
-- -- x y : Nat 
-- parens multibind 
-- -- (x y : Nat)
-- many1 multibind
-- -- (x y : Nat) (z : Nat)
many1MultiBinding :: P [(Name, SType)]
many1MultiBinding = do 
  xs <- many1 (parens multibinding)
  return $ concat xs

-- (x y : Nat) (z : Nat)
binders :: P [(Name, SType)]
binders =  many1MultiBinding
  <|> (binding >>= \x -> return [x])
  
-- (x:Nat y:Nat z:Nat) -> (x y z : Nat)
lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         binds <- binders
         reservedOp "->"
         t <- expr
         return (SLam i binds t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         binds <- binders
         reservedOp "->"
         t <- expr
         return (SFix i binds t)

isRecursive :: P Bool
isRecursive = try (reserved "rec" >> return True) <|> return False

letFunction :: P [(Name, SType)]
letFunction = do
  name <- var
  binds <- binders
  reserved ":"
  myType <- typeP
  return ((name,myType) : binds)

letexp :: P STerm
letexp = do
  i <- getPos
  reserved "let"
  recursive <- isRecursive
  binds <- bindingLet
  reservedOp "="
  def <- expr
  reserved "in"
  body <- expr
  return (SLet i recursive binds def body)

-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> printOp <|> fix <|> letexp

bindingLet :: P [(Name, SType)]
bindingLet = try ((parens binding <|> binding) >>= \b -> return [b]) <|> letFunction

-- | Parser de declaraciones Let
letDecl :: P (SDecl STerm)
letDecl = do
      i <- getPos
      reserved "let"
      recursive <- isRecursive
      binds <- bindingLet
      reservedOp "="
      t <- expr
      return (SDecl i recursive binds t)

-- | Parser de declaraciones Typedef
typeDefDecl :: P (SDecl STerm)
typeDefDecl = do
     i <- getPos
     reserved "type"
     alias <- tyIdentifier
     reservedOp "="
     t <- typeP
     return (SDeclTy i alias t)

-- | Parser de declaraciones
decl :: P (SDecl  STerm)
decl = try letDecl <|> typeDefDecl


-- | Parser de programas (listas de declaraciones) 
program :: P [SDecl STerm]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (SDecl STerm) STerm)
declOrTm =  try (Right <$> expr) <|> (Left <$> decl)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
