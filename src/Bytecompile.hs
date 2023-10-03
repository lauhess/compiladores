{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List (intercalate)
import Data.Char
import Eval (semOp)

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }

type Env = [Val]
data Val = I Int | Fun Env Bytecode | RA Env Bytecode

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

-- Compila un término a bytecode
bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc t = case t of
  V _ _ -> failFD4 "implementame!"
  Const _ (CNat n) -> return [CONST, fromIntegral n]
  Lam _ _ _ (Sc1 t1) -> do
    bt <- bcc t
    return $ [FUNCTION, length bt] ++ bt ++ [RETURN]
  App _ t1 t2 -> do
    b1 <- bcc t1
    b2 <- bcc t2
    return $ b1 ++ b2 ++ [CALL]
  Print _ str t1 -> do
    bt <- bcc t
    return $ [length str] ++ string2bc str ++ [PRINT] ++ bt ++ [PRINTN]
  BinaryOp _ Add t1 t2 -> do
    b1 <- bcc t1
    b2 <- bcc t2
    return $ b1 ++ b2 ++ [ADD]
  BinaryOp _ Sub t1 t2 -> do
    b1 <- bcc t1
    b2 <- bcc t2
    return $ b1 ++ b2 ++ [SUB]
  Fix _ _ _ _ _ (Sc2 t1) -> do
    b1 <- bcc t1
    return $ [FUNCTION, length b1] ++ b1 ++ [FIX]
  IfZ _ c t1 t2 -> do
    bc <- bcc c
    b1 <- bcc t1
    b2 <- bcc t2
    return $ bc ++ [JUMP, length b1] ++ b1 ++ [JUMP, length b2] ++ b2
    -- [c, JUMP, l1, x1, x2, ..., xn, JUMP, l2, y1, y2, ..., ym]
    --  0, 1,     2, 2 + 1, 2 + 2, 2 + n, 2 + n + 1, 2+n+2,2+n+m]   
    -- - Si c == 1, seguimos ejecutando en la vm, 
    --   luego llegaremos a un JUMP que indica el comienzo del "else" 
    --   que obviamente saltearemos
    -- - Sino, hacemos un salto de n + 1 (JUMP y el largo de b1), y ejecutamos
    --   la condición del else.
    -- ToDo: Pensar casos de ifz anidados
  Let _ _ _ t1 (Sc1 t2) -> do
    b1 <- bcc t1
    b2 <- bcc t2
    return $ b1 ++ [SHIFT] ++ b2 ++ [DROP]

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = failFD4 "implementame!"

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename


runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = void $ runBC' bc [] []

runBC' :: MonadFD4 m => Bytecode -> Env -> [Val] -> m Val
runBC' bs e s = case bs of
  []              -> (return . head) s
  (NULL:xs)       -> runBC' xs e s
  (RETURN:xs)     -> let (val : RA e' bs' : s') = s
                      in runBC' bs' e (val : s')
  (CONST:i:xs)    -> runBC' xs e (I i:s)
  (ACCESS:i:xs)   -> runBC' xs e ( e !! i : s)
  (FUNCTION:i:xs) -> let bs' = take i xs
                      in runBC' xs e (Fun e bs' : s)
  (CALL:xs)       -> let (v: (Fun ef cf) : s') = s
                      in runBC' cf (v:ef) (RA e xs:s)
  (ADD:xs)        -> let (I x : I y : s') = s
                      in runBC' xs e (I (semOp Add x y):s')
  (SUB:xs)        -> let (I x : I y : s') = s
                      in runBC' xs e (I (semOp Sub x y):s')
  (FIX:xs)        -> undefined
  (STOP:xs)       -> undefined
  (JUMP:i:xs)     -> undefined
  (SHIFT:xs)      -> runBC' xs (head s : e) (tail s)
  (DROP:xs)       -> runBC' xs (tail e) s
  (PRINT:xs)      -> undefined
  (PRINTN:xs)     -> undefined
  (x:xs)          -> undefined
