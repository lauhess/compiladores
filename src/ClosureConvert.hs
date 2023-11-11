module ClosureConvert where

import Lang
import IR
import Control.Monad.Writer (Writer, MonadWriter (tell, listen), runWriter)
import PPrint (freshen)
import MonadFD4
import Subst
import qualified GHC.Base
import Debug.Trace

type CCState = StateT Int (Writer [IrDecl]) Ir

-- term2ir :: TTerm -> Ir
-- term2ir = undefined

-- ty2irTy :: Ty -> IrTy
-- ty2irTy = undefined

-- decl2irDecl :: Decl TTerm -> IrDecl
-- decl2irDecl (Decl _ name NatTy t) = IrVal name IrInt (term2ir t)
-- decl2irDecl (Decl _ name (FunTy declTy retTy) t) = IrFun name (head $ ty2irTy retTy) (ty2irTy declTy) (term2ir t)

closureConvert :: TTerm -> [Name] -> CCState
closureConvert t bounds = trace (show t ++ "\n") $ case t of
  V _ (Bound n) -> error "Falto consumir alguna lambda"
  V _ (Free n) -> return $ IrVar n
  V _ (Global n) -> return $ IrGlobal n
  Const _ co@(CNat n) -> return $ IrConst co
  Lam _ fn ty (Sc1 tm) -> do
    let (names, tm') = cfreshen bounds fn tm -- Libero un nuevo nombre
        fn' = "_" ++ head names              -- Nombre nuevo para la funcion
        varLibres = map IrVar (freeVars tm') -- Lista de valiables libres
        cloName = "_" ++ fn'                 -- Nombre de la closure
    body <- closureConvert tm' bounds
    -- tell _
    let bodyBoundingVars = foldr (\(i, IrVar name) body'  ->
         IrLet name IrInt (IrAccess (IrVar cloName) IrInt i) body')
          body
          (zip [1..] varLibres)
    tell [IrFun cloName IrClo [(fn', IrInt)] bodyBoundingVars]
    return $ MkClosure fn' varLibres
  App _ t1 t2 -> do
    let dummyName = freshen bounds "_dummy"
    ir1 <- closureConvert t1 (dummyName:bounds)
    ir2 <- closureConvert t2 (dummyName:bounds)
    return $ IrLet dummyName IrFunTy ir1 (IrCall (IrAccess (IrVar dummyName) IrFunTy 0) [ir1,ir2] IrInt)
    -- return $ IrCall ir1 [ir2] IrInt
  Print _ str tm -> do
      ir1 <- closureConvert tm bounds
      return $ IrPrint str ir1
  BinaryOp _ op t1 t2 -> do
    ir1 <- closureConvert t1 bounds
    ir2 <- closureConvert t2 bounds
    return $ IrBinaryOp op ir1 ir2
  Fix _ fn ty str ty' (Sc2 tm) -> do
    let (names, tm') = cfreshen2 bounds fn tm -- Libero un nuevo nombre
        fn' = "_" ++ head names               -- Nombre nuevo para la funcion
        varLibres = map IrVar (freeVars tm')  -- Lista de valiables libres
        cloName = "_" ++ fn'                  -- Nombre de la closure
    body <- closureConvert tm' bounds
    -- tell _
    let bodyBoundingVars = foldr (\(i, IrVar name) body'  ->
         IrLet name IrInt (IrAccess (IrVar cloName) IrInt i) body')
          body
          (zip [1..] varLibres)
    tell [IrFun cloName IrClo [(fn', IrInt)] bodyBoundingVars]
    return $ MkClosure fn' varLibres
  IfZ _ t1 t2 t3 -> do
    ir1 <- closureConvert t1 bounds
    ir2 <- closureConvert t2 bounds
    ir3 <- closureConvert t3 bounds
    return $ IrIfZ ir1 ir2 ir3
  Let _ name ty t1 (Sc1 t2) -> do
    ir1 <- closureConvert t1 bounds
    let (bounds', t2') = cfreshen bounds name t2
    ir2 <- closureConvert t2' bounds'
    return $ IrLet name IrInt ir1 ir2

cfreshen :: [Name] -> Name -> TTerm -> ([Name], TTerm)
cfreshen ns n tm = let newName = "_" ++ freshen ns n
                       newTree = open newName (Sc1 tm)
                    in (newName:ns, newTree)

cfreshen2 :: [Name] -> Name -> TTerm -> ([Name], TTerm)
cfreshen2 ns n tm = let name1 = "_" ++ freshen ns n
                        name2 = "_" ++ freshen (name1:ns) n
                        newNames = name1:name2:ns
                        newTree = open2 name1 name2 (Sc2 tm)
                    in (newNames, newTree)

runCC :: Module -> IrDecls
runCC [] = IrDecls []
runCC (m:ms) = let (Decl _ name ty t) = m
                   (_, decls) = runWS t 0 []
                   decls' = decls ++ irDecls (runCC ms)
                in trace (show (IrDecls decls')) (IrDecls decls')

runWS :: TTerm -> Int -> [Name] -> ((Ir, Int), [IrDecl])
runWS t s bounds = runWriter $ runStateT (closureConvert t bounds) s