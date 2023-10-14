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
import Subst
import PPrint (pp)

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }

type Env = [Val]
data Val = I Int | Fun Env Bytecode | RA Env Bytecode 
instance Show Val where 
  show (I n) = show n
  show (Fun _ b) = "Fun [" ++ showBC b ++ "]"
  show (RA _ b) = "RA [" ++ showBC b ++ "]"

-- ToDo: Modificar  para soportar varios modos de debug: Solo bytecode, solo pila, ambos, ninguno
-- Usar potencias dos para representar los modos de debug
printVals :: MonadFD4 m => Bool -> Bytecode -> Env -> [Val] -> m ()
printVals True x e vs = printFD4 $  "Next: " ++ intercalate "; " (showOps x)  ++ 
                                   "\nEnv: " ++ intercalate ", " (map show e) ++ 
                                   "\nPila: " ++ intercalate ", " (map show (take 10 vs)) ++ "\n"
printVals False _ _ _ = return ()

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
pattern CJUMP    = 8
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
showOps (CJUMP:i:xs)     = ("CJUMP off=" ++ show i) : showOps xs
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
bcc t = pp t  >> case t of
  V _ (Free _) -> failFD4 "implementame! (Bytecompile:114)"
  V _ (Bound i) -> return [ACCESS, i]
  V _ (Global _) -> failFD4 "implementame! (Bytecompile:116)"
  Const _ (CNat n) -> return [CONST, fromIntegral n]
  Lam _ _ _ (Sc1 t1) -> do
    printFD4 $ show t1
    bt <- bcc t1
    return $ [FUNCTION, length bt + 1] ++ bt ++ [RETURN]
  App _ t1 t2 -> do
    b1 <- bcc t1
    b2 <- bcc t2
    return $ b1 ++ b2 ++ [CALL]
  Print _ str t1 -> do
    bt <- bcc t1
    let sbc = string2bc str
    return $ [PRINT] ++ sbc ++ [NULL] ++ bt ++ [NULL, PRINTN] 
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
    return $ [FUNCTION, length b1 + 1] ++ b1 ++ [RETURN, FIX]
  IfZ _ c t1 t2 -> do
    bc <- bcc c
    b1 <- bcc t1
    b2 <- bcc t2
    return $ bc ++ [CJUMP, length b1 + 2] ++ b1 ++ [JUMP, length b2] ++ b2
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
-- bytecompileModule m = bytecompileModule' m []
bytecompileModule [] = return [STOP]
-- bytecompileModule m = bcc (decl2term m) >>= (\bc -> return (bc ++ [STOP]))
bytecompileModule m = do
    let t = decl2term m
    pt <- pp t
    printFD4 pt
    bc <- bcc t
    -- printFD4 $ intercalate "\n" $ showOps bc
    return (bc ++ [STOP])
-- bytecompileModule' :: MonadFD4 m => Module -> Bytecode -> m Bytecode
-- bytecompileModule' [] bcs = return $ bcs ++ [STOP]
-- -- bytecompileModule' ((Decl _ x ty t):ds) bcs = do
-- --   let (Sc1 t') = close x t
-- --   bcc_t' <- bcc t'
-- --   bytecompileModule' ds (bcc_t' ++ bcs)
-- -- bytecompileModule' ((Decl _ x ty t):ds) bcs = 


decl2term :: Module -> TTerm
decl2term [Decl info x ty t] = liverator t
decl2term ((Decl info x ty t):ds) =
  let ts = decl2term ds
      t' = liverator t
      body = close x ts
  in Let (info, ty) x ty t' body
decl2term [] = undefined

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
runBC' bs e s = printVals False bs e s >> case bs of
  []              -> return (head s)
  (NULL:xs)       -> runBC' xs e s
  (RETURN:xs)     -> let (val : RA e' bs' : s') = s
                      in runBC' bs' e' (val : s')
  (CONST:i:xs)    -> runBC' xs e (I i:s)
  (ACCESS:i:xs)   -> runBC' xs e ( e !! i  : s)
  (FUNCTION:i:xs) -> let bs' = take i xs
                      in runBC' (drop i xs) e (Fun e bs' : s)
  (CALL:xs)       -> let (v: (Fun ef cf) : s') = s
                      in runBC' cf (v:ef) (RA e xs:s')
  (ADD:xs)        -> let (I x : I y : s') = s
                      in runBC' xs e (I (semOp Add y x):s')
  (SUB:xs)        -> let (I x : I y : s') = s
                      in runBC' xs e (I (semOp Sub y x):s')
  (FIX:xs)        -> let (Fun ef bc : s') = s  
                         efix      = Fun efix bc : e
                      in runBC' xs e (Fun efix bc : s')
  (STOP:xs)       -> return (head s)
  (CJUMP:i:xs)    -> let (I c : s') = s 
                      in case c of 
                          0 -> runBC' xs e s' 
                          _ -> runBC' (drop i xs) e s'
  (JUMP:i:xs)     -> runBC' (drop i xs) e s
  (SHIFT:xs)      -> runBC' xs (head s : e) (tail s)
  (DROP:xs)       -> runBC' xs (tail e) s
  (PRINT:xs)      -> let (str, bc') = span (/=NULL) xs 
                      in ( liftIO . putStr) (bc2string str) >> runBC' bc' e s
  (PRINTN:xs)     -> let (I n : _) = s
                      in printFD4 (show n) >> runBC' xs e s
  (x:xs)          -> failFD4 $ "opcode desconocido: " ++ show x


liverator :: TTerm -> TTerm
liverator   v@(V p (Bound i)) = v
liverator   v@(V p (Free x)) = v
liverator   (V p (Global x)) = V p (Free x)
liverator (Lam p y ty (Sc1 t))   = Lam p y ty (Sc1 (liverator t))
liverator (App p l r)   = App p (liverator l) (liverator r)
liverator (Fix p f fty x xty (Sc2 t)) = Fix p f fty x xty (Sc2 (liverator t))
liverator (IfZ p c t e) = IfZ p (liverator c) (liverator t) (liverator e)
liverator t@(Const _ _) = t
liverator (Print p str t) = Print p str (liverator t)
liverator (BinaryOp p op t u) = BinaryOp p op (liverator t) (liverator u)
liverator (Let p v vty m (Sc1 o)) = Let p v vty (liverator m) (Sc1 (liverator o))