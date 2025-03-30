{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
module ClosureConvert where

import Lang
import IR
import Control.Monad.Writer (Writer, MonadWriter (tell), runWriter)
import MonadFD4
import Subst

type CCState a = StateT Int (Writer [IrDecl]) a

type TyName = (IrTy, Name)

closureConvert :: TTerm -> CCState Ir
closureConvert t = case t of
  V _ (Bound n) -> error "Falto consumir alguna lambda"
  V _ (Free n) -> return $ IrVar n
  V _ (Global n) -> return $ IrGlobal n
  Const _ co@(CNat n) -> return $ IrConst co
  -- Lam (_, FunTy _ ty) fn tyVar (Sc1 tm) -> do
    -- ToDo: Usar nombre de la funcino de ser posible (excepcion:)
  (Lam (_, FunTy f tyVar tyRet) n _ body@(Sc1 b)) -> do -- ToDo: Revisar primer param FunTy
    nombreFuncion <- freeName (if f == "" then "lam" else f)
    nombreArg <- freeName n

    body' <- closureConvert $ open nombreArg body

    let fv = freeVarsTy b

    closure <- freeName (nombreFuncion ++ "clos")

    let cuerpo        = args2vars fv body' closure
        tipoRetorno   = convertType tyRet
        tipoArgumento = convertType tyVar

    let decl = IrFun nombreFuncion tipoRetorno [(closure, IrClo), (nombreArg, tipoArgumento)] cuerpo
    tell [decl]

    return $ MkClosure nombreFuncion $ map (IrVar . fst) fv
  Lam {} -> error "Lam: Tipo invalido"
  App (_,ty) t1 t2 -> do
    dummyName <- freeName "App"
    ir1 <- closureConvert t1
    ir2 <- closureConvert t2
    return $ IrLet dummyName IrClo ir1 (IrCall (IrAccess (IrVar dummyName) IrFunTy 0) [IrVar dummyName,ir2] (convertType ty))
  Print _ str tm -> do
      ir1 <- closureConvert tm
      temp <- freeName "temp"
      return $ IrLet temp IrInt ir1 (IrPrint str (IrVar temp))
  BinaryOp _ op t1 t2 -> do
    ir1 <- closureConvert t1
    ir2 <- closureConvert t2
    return $ IrBinaryOp op ir1 ir2
  Fix (_, FunTy _ _ ty) fn fty vn vty body@(Sc2 b) -> do -- ToDo: Revisar primer param FunTy
    nombreFuncion <- freeName ("fix_" ++ fn)
    nombreArg <- freeName vn
    closure <- freeName ("clos" ++ nombreFuncion)

    body'' <- closureConvert $ open2 closure nombreArg body

    let fv = freeVarsTy b
        cuerpo = args2vars fv body'' closure
        tipoRetorno = convertType ty
        decl = IrFun nombreFuncion tipoRetorno [(closure, IrClo), (nombreArg, IrInt)] cuerpo

    tell [decl]

    return $ MkClosure nombreFuncion $ map (IrVar . fst) fv
  Fix {} -> error "Fix: Tipo invalido"
  IfZ _ t1 t2 t3 -> do
    ir1 <- closureConvert t1
    ir2 <- closureConvert t2
    ir3 <- closureConvert t3
    return $ IrIfZ ir1 ir2 ir3
  Let _ name ty t1 body@(Sc1 t2) -> do
    ir1   <- closureConvert t1
    name' <- freeName name
    ir2   <- closureConvert $ open name' body
    return $ IrLet name' (convertType ty) ir1 ir2

runCC :: [Decl TTerm] -> IrDecls
runCC m = let mon = runCC' m
          in IrDecls $ (snd . runWriter . runStateT mon) 0

runCC' :: Module -> CCState ()
runCC' [Decl _ name ty t] = do
  r <- closureConvert t
  tell [IrVal name (convertType ty) r]
  return ()
runCC'((Decl _ name ty t):ms) = do
  r <- closureConvert t
  tell [IrVal name (convertType ty) r]
  runCC' ms
runCC' _ = error "No se puede convertir"

convertType :: Ty -> IrTy
convertType (NatTy _) = IrInt
convertType (FunTy _ _ _) = IrClo

freeName :: Name -> CCState Name
freeName prefix = do
    n <- get
    put $ n + 1
    return (prefix ++ "_" ++  show n)

args2vars :: [(Name, Ty)] -> Ir -> Name -> Ir
args2vars fv t closure =
    foldr   (\((v, ty), i) ir -> IrLet v (convertType ty) (IrAccess (IrVar closure) (convertType ty) i) ir)
            t
            (zip fv [1..])