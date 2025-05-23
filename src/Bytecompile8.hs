{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

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
module Bytecompile8
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
    ( BinaryOp(Sub, Add),
      Const(CNat),
      Decl(Decl),
      Module,
      Scope(Sc1),
      Scope2(Sc2),
      TTerm,
      Tm(Let, V, Lam, App, Fix, IfZ, Const, Print, BinaryOp),
      Var(Free, Bound, Global) )
import MonadFD4

import Data.Binary
import Data.Binary.Get ( isEmpty )
import qualified Data.ByteString as BSS
import qualified Data.ByteString.Lazy as BS
import Data.List (intercalate)
import qualified Data.Text as T
import qualified Data.Text.Encoding as E

import EncodingUtils (int2bs, bs2int, skipBs)
import Eval (semOp)
import Global (Statistics(..), GlEnv (statistics), DebugOptions(..))
import Optimization (optimizeTerm)
import PPrint (pp)
import Subst
import GHC.Base (when)      -- Para CI
import Control.Monad (void) -- Para CI

type Opcode = Word8
type Bytecode = [Word8]

newtype Bytecode8 = BC { un8 :: [Word8] }

type Env = [Val]
data Val = I Int | Fun Env Bytecode | RA Env Bytecode
instance Show Val where
  show (I n) = show n
  show (Fun _ b) = "Fun [" ++ showBC b ++ "]"
  show (RA _ b) = "RA [" ++ showBC b ++ "]"

-- ToDo: Modificar  para soportar varios modos de debug: Solo bytecode, solo pila, ambos, ninguno
-- Usar potencias dos para representar los modos de debug
--printVals :: MonadFD4 m => Bool -> Bytecode -> Env -> [Val] -> m ()
--printVals True x e vs = printFD4 $  "Next: " ++ intercalate "; " (showOps x)  ++
--                                   "\nEnv: " ++ intercalate ", " (map show e) ++
--                                   "\nPila: " ++ intercalate ", " (map show (take 10 vs)) ++ "\n"


printNextBytecode :: MonadFD4 m => Bytecode -> m ()
printNextBytecode x = printFD4 $  "Next: " ++ intercalate "; " (showOps x)

printEnv :: (MonadFD4 m, Show a) => [a] -> m ()
printEnv e = printFD4 $ "Env: " ++ intercalate ", " (map show e)

printStack :: (MonadFD4 m, Show a1, Show a2) => [a1] -> [a2] -> m ()
printStack e vs = printFD4 $ "Pila: " ++ intercalate ", " (map show (take 10 vs)) ++ "\n"

printVals' :: MonadFD4 m => Bytecode -> Env -> [Val] -> DebugOptions -> m ()
printVals' x e vs opts =
      when (enabledPrintBytecode opts) (printNextBytecode x)
  >>  when (enablePrintEnv       opts) (printEnv e)
  >>  when (enabledPrintStack    opts) (printStack e vs)

printVals :: MonadFD4 m => Bytecode -> Env -> [Val] -> m ()
printVals x e vs = getByteCodeDebugOptions >>= maybe (return ()) (printVals' x e vs)

{- Esta instancia explica como codificar y decodificar Bytecode de 8 bits -}
instance Binary Bytecode8 where
  put (BC bs) = mapM_ putWord8 bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord8
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
pattern TAILCALL = 16
pattern DISCARD = 17

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:xs)     =  let (n, xs') = bs2int xs
                          in ("CONST " ++ show n) : showOps xs'
showOps (ACCESS:xs)    = let (n, xs') = bs2int xs
                         in ("ACCESS " ++ show n) : showOps xs'
--showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (FUNCTION:xs)    = let (n, xs') = bs2int xs
                          in ("FUNCTION len=" ++ show n) : showOps xs'
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
--showOps (CJUMP:i:xs)     = ("CJUMP off=" ++ show i) : showOps xs
showOps (CJUMP:xs)       = let (n, xs') = bs2int xs
                          in ("CJUMP off=" ++ show n) : showOps xs'
--showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (JUMP:xs)        = let (n, xs') = bs2int xs
                          in ("JUMP off=" ++ show n) : showOps xs'
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (DISCARD:xs)     = "DISCARD" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

-- Compila un término a bytecode
bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc t = case t of
  V _ (Free _) -> failFD4 "implementame! (Bytecompile:155)"
  V _ (Bound i) -> let bs = int2bs (fromIntegral i) in return (ACCESS:bs)
  V _ (Global _) -> failFD4 "implementame! (Bytecompile:157)"
  Const _ (CNat n) -> return $ CONST : int2bs n
  Lam _ _ _ (Sc1 t1) -> do
    bt <- bctc t1
    let lengthb = int2bs (length bt)
    return $ [FUNCTION] ++ lengthb ++ bt
  App _ t1 t2 -> do
    b1 <- bcc t1
    b2 <- bcc t2
    return $ b1 ++ b2 ++ [CALL]
  Print _ str t1 -> do
    bt <- bcc t1
    let sbc = string2bc str
    return $ bt ++ [PRINT] ++ sbc ++ [NULL] ++ [PRINTN]
  BinaryOp _ Add t1 t2 -> do
    b1 <- bcc t1
    b2 <- bcc t2
    return $ b1 ++ b2 ++ [ADD]
  BinaryOp _ Sub t1 t2 -> do
    b1 <- bcc t1
    b2 <- bcc t2
    return $ b1 ++ b2 ++ [SUB]
  Fix _ _ _ _ _ (Sc2 t1) -> do
    b1 <- bctc t1
    let lengthb1 = int2bs (length b1)
    return $ [FUNCTION] ++ lengthb1 ++ b1 ++ [FIX]
  IfZ _ c t1 t2 -> do
    bc <- bcc c
    b1 <- bcc t1
    b2 <- bcc t2
    let lengthCJump = int2bs (length b1 + 2)
    let lb2 = length b2
    let lengthJump = int2bs lb2
    return $ bc ++ [CJUMP] ++ lengthCJump ++ longJump b1 (length lengthJump + lb2) ++ [JUMP] ++ lengthJump ++ b2
  Let i' "_" _ t1 (Sc1 t2) -> do
    b1 <- bcc t1
    b2 <- bcc $ varChanger 0  varLibres varBound t2
    return $ b1 ++ [DISCARD] ++ b2
    where
      varLibres n p x = V p (Free x)
      varBound n p i  = if n < i then V p (Bound (i - 1)) else V p (Bound i)
  Let i' _ _ t1 (Sc1 t2) -> case t2 of
    (Print _ s (V _ (Bound 0))) -> bcc (Print i' s t1)
    Let i _ _ (Print _ s (V _ (Bound 0))) (Sc1 t3) -> do
      b1 <- bcc (Print i s t1)
      b2 <- bcc (letSimp t3)
      return $ b1 ++ [SHIFT] ++ b2 ++ [DROP]
    (V _ (Bound 0)) -> bcc t1
    _ -> do
      b1 <- bcc t1
      b2 <- bcc t2
      return $ b1 ++ [SHIFT] ++ b2 ++ [DROP]

bctc :: MonadFD4 m => TTerm -> m Bytecode
bctc t = case t of
  App _ t1 t2 -> do
    b1 <- bcc t1
    b2 <- bcc t2
    return $ b1 ++ b2 ++ [TAILCALL]
  IfZ _ c t1 t2 -> do
    bc <- bcc c
    b1 <- bctc t1
    b2 <- bctc t2
    let lengthCJump = int2bs (length b1 + 2)
    let lengthJump = int2bs (length b2)
    return $ bc ++ [CJUMP] ++ lengthCJump ++ b1 ++ [JUMP] ++ lengthJump ++ b2
  Let i' "_" _ t1 (Sc1 t2) -> do
    b1 <- bcc t1
    b2 <- bctc $ varChanger 0  varLibres varBound t2
    return $ b1 ++ [DISCARD] ++ b2
    where
      varLibres n p x = V p (Free x)
      varBound n p i  = if n < i then V p (Bound (i - 1)) else V p (Bound i)
  Let i' _ _ t1 (Sc1 t2) -> case t2 of
    (Print _ s (V _ (Bound 0))) -> bctc (Print i' s t1)
    Let i _ _ (Print _ s (V _ (Bound 0))) (Sc1 t3) -> do
      b1 <- bcc (Print i s t1)
      b2 <- bctc (letSimp t3)
      return $ b1 ++ [SHIFT] ++ b2
    (V _ (Bound 0)) -> bctc t1
    _ -> do
      b1 <- bcc t1
      b2 <- bctc t2
      return $ b1 ++ [SHIFT] ++ b2
  _ -> do
    bt <- bcc t
    return $ bt ++ [RETURN]


-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc =  BSS.unpack . E.encodeUtf8 . T.pack
-- string2bc = map ord

bc2string :: Bytecode -> String
bc2string = T.unpack . E.decodeUtf8 . BSS.pack
-- bc2string = map chr

-- ToDo: Pese a que funciona sin obtener el tamaño correcto de i habría que ser consistentes
optimizeBytecode :: Bytecode -> Bytecode
optimizeBytecode bs = case bs of
  [] -> []
  (CONST:xs)    -> skipAndOptimize CONST xs
  (ACCESS:xs)   -> skipAndOptimize ACCESS xs
  (FUNCTION:xs) -> skipAndOptimize FUNCTION xs
  (CJUMP:xs)    -> skipAndOptimize CJUMP xs
  (JUMP:xs)     -> skipAndOptimize JUMP xs
  (PRINT:xs)    ->
    case span (/= NULL) xs of
      (str, rest) -> PRINT : str ++ optimizeBytecode rest
  (DROP:xs)     ->
    case optimizeBytecode xs of
      []             -> []
      xs'@(RETURN:_) -> xs'
      xs'@[STOP]     -> xs'
      xs'            -> DROP : xs'
  (x:xs)        -> x : optimizeBytecode xs
  where
    skipAndOptimize op xs' =
      case skipBs xs' of
        (num, rest) -> op : num ++ optimizeBytecode rest

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule [] = return [STOP]
bytecompileModule m@((Decl info name ty _):_) = do
    let t' = decl2term m
    opt <- getOpt
    t <- if opt then optimizeTerm t' else return t'
    pt <- pp t
    bc <- bcc t
    let optBC = optimizeBytecode bc
    return (optBC ++ [STOP])

decl2term :: Module -> TTerm
decl2term [Decl info x ty t] = freeTerm t
decl2term ((Decl info x ty t):ds) =
  let ts = decl2term ds
      t' = freeTerm t
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
bcRead filename = (map fromIntegral <$> un8) . decode <$> BS.readFile filename


runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = void $ inicializarStats >> runBC' bc [] []

runBC' :: MonadFD4 m => Bytecode -> Env -> [Val] -> m Val
runBC' bs e s = printVals bs e s >> incOpCount >> incOpMaxPilaSize s >> case bs of
  []              -> return (head s)
  (NULL:xs)       -> runBC' xs e s
  (RETURN:xs)     -> let (val : RA e' bs' : s') = s
                      in runBC' bs' e' (val : s')
  (CONST:xs)      -> let (n, xs') = bs2int xs
                      in runBC' xs' e (I n : s)
  (ACCESS:xs)     -> let (n, xs') = bs2int xs
                      in runBC' xs' e (e !! n : s)
  (FUNCTION:xs)   -> let (n, xs') = bs2int xs
                      in incOpClaus >> runBC' (drop n xs') e (Fun e (take n xs') : s)
  (CALL:xs)       -> let (v: (Fun ef cf) : s') = s
                      in incOpClaus >> runBC' cf (v:ef) (RA e xs:s')
  (ADD:xs)        -> let (I x : I y : s') = s
                      in runBC' xs e (I (semOp Add y x):s')
  (SUB:xs)        -> let (I x : I y : s') = s
                      in runBC' xs e (I (semOp Sub y x):s')
  (FIX:xs)        -> let (Fun ef bc : s') = s
                         efix      = Fun efix bc : e
                      in incOpClaus >> runBC' xs e (Fun efix bc : s')
  (STOP:xs)       -> return (head s)
  (CJUMP:xs)      -> let (n, xs')   = bs2int xs
                         (I c : s') = s
                      in case c of
                          0 -> runBC' xs' e s'
                          _ -> runBC' (drop n xs') e s'
  (JUMP:xs)     -> let (n, xs') = bs2int xs
                    in runBC' (drop n xs') e s
  (SHIFT:xs)      -> runBC' xs (head s : e) (tail s)
  (DROP:xs)       -> runBC' xs (tail e) s
  (DISCARD:xs)    -> runBC' xs e (tail s)
  (PRINT:xs)      -> let (str, bc') = span (/=NULL) xs
                      in ( liftIO . putStr) (bc2string str) >> runBC' bc' e s
  (PRINTN:xs)     -> let (I n : _) = s
                      in printFD4 (show n) >> runBC' xs e s
  (TAILCALL:xs)   -> let (v : Fun eg cg :  s') = s
                      in runBC' cg (v : eg) s'
  (x:xs)          -> failFD4 $ "opcode desconocido: " ++ show x

freeTerm :: TTerm -> TTerm
freeTerm   v@(V p (Bound i)) = v
freeTerm   v@(V p (Free x)) = v
freeTerm   (V p (Global x)) = V p (Free x)
freeTerm (Lam p y ty (Sc1 t))   = Lam p y ty (Sc1 (freeTerm t))
freeTerm (App p l r)   = App p (freeTerm l) (freeTerm r)
freeTerm (Fix p f fty x xty (Sc2 t)) = Fix p f fty x xty (Sc2 (freeTerm t))
freeTerm (IfZ p c t e) = IfZ p (freeTerm c) (freeTerm t) (freeTerm e)
freeTerm t@(Const _ _) = t
freeTerm (Print p str t) = Print p str (freeTerm t)
freeTerm (BinaryOp p op t u) = BinaryOp p op (freeTerm t) (freeTerm u)
freeTerm (Let p v vty m (Sc1 o)) = Let p v vty (freeTerm m) (Sc1 (freeTerm o))

inicializarStats :: MonadFD4 m => m ()
inicializarStats = getProf >>= \case
  True -> modify (\s -> s {
    statistics = StatsBytecode 0 0 0
  })
  _ -> modify (\s -> s {
    statistics = Dummy
  })

incOpCount :: MonadFD4 m => m ()
incOpCount = gets statistics >>= \case
  (StatsBytecode op cl mp) -> modify (\s -> s {
      statistics = StatsBytecode (op + 1) cl mp
    })
  (StatsCEK _ _) -> failFD4 "Tipo de estadística equivocado."
  _ -> return ()

incOpClaus :: MonadFD4 m => m ()
incOpClaus = gets statistics >>= \case
  (StatsBytecode op cl mp) -> modify (\s -> s {
      statistics = StatsBytecode op (cl + 1) mp
    })
  (StatsCEK _ _) -> failFD4 "Tipo de estadística equivocado."
  _ -> return ()

incOpMaxPilaSize :: MonadFD4 m => [Val] -> m ()
incOpMaxPilaSize stack = gets statistics >>= \case
  (StatsBytecode op cl mp) -> modify (\s -> s {
      statistics = StatsBytecode op cl (max mp (length stack))
    })
  (StatsCEK _ _) -> failFD4 "Tipo de estadística equivocado."
  _ -> return ()

longJump :: Bytecode -> Int -> Bytecode
longJump bs j = case bs of
  [] -> []
  (CONST:xs) -> CONST : skipAndJump xs
  (ACCESS:xs) -> ACCESS : skipAndJump xs
  (FUNCTION:xs) -> FUNCTION : skipAndJump xs
  (CJUMP:xs) -> CJUMP : skipAndJump xs
  (JUMP:n:xs) ->
    let (num, xs') = skipBs xs
        (num', _) = bs2int num
    in if length xs' == num'
         then JUMP : int2bs (num' + j + 1) ++ longJump xs' j
         else JUMP : num ++ longJump xs' j
  (PRINT:xs) ->
    let (str, rest) = span (/= NULL) xs
    in PRINT : str ++ longJump rest j
  (x:xs) -> x : longJump xs j
  where
    skipAndJump xs = let (num, xs') = skipBs xs in num ++ longJump xs' j

letSimp :: TTerm -> TTerm
letSimp = varChanger 0 (\ _ p x -> V p (Free x)) (\ n p i -> if i < n then V p (Bound i) else V p (Bound (i - 1)))