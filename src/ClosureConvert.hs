module ClosureConvert where

import Lang
import IR
import Control.Monad.Writer (Writer, MonadWriter (tell), runWriter)
import PPrint (freshen)
import MonadFD4
import Subst
import Debug.Trace

type CCState a = StateT Int (Writer [IrDecl]) a

type TyName = (IrTy, Name)

-- term2ir :: TTerm -> Ir
-- term2ir = undefined

-- ty2irTy :: Ty -> IrTy
-- ty2irTy = undefined

-- decl2irDecl :: Decl TTerm -> IrDecl
-- decl2irDecl (Decl _ name NatTy t) = IrVal name IrInt (term2ir t)
-- decl2irDecl (Decl _ name (FunTy declTy retTy) t) = IrFun name (head $ ty2irTy retTy) (ty2irTy declTy) (term2ir t)

closureConvert :: TTerm -> [TyName] -> CCState Ir
closureConvert t bounds = case t of
  V _ (Bound n) -> error "Falto consumir alguna lambda"
  V _ (Free n) -> return $ IrVar n
  V _ (Global n) -> return $ IrGlobal n
  Const _ co@(CNat n) -> return $ IrConst co
  Lam _ fn ty (Sc1 tm) -> do
    let a@(names, tm') = cfreshen bounds (convertType ty, fn) tm -- Libero un nuevo nombre
        fn' = (snd . head) names              -- Nombre nuevo para la funcion
        varLibres = map IrVar (freeVars tm) -- Lista de valiables libres
        cloName = "_" ++ fn'                 -- Nombre de la closure
    body <- closureConvert tm' names
    -- tell _
    let bodyBoundingVars = foldr (\(i, (ty', name)) body'  ->
         IrLet name ty' (IrAccess (IrVar cloName) IrInt i) body')
          body
          (zip [1..] bounds)
    tell [IrFun cloName (convertType ty) [("x", IrClo),(fn', IrInt)] bodyBoundingVars]
    return $ MkClosure cloName varLibres
  App (_,ty) t1 t2 -> do
    trace (show ty) $ return ()
    let dummyName = freshen (map snd bounds) "_dummy"
    ir1 <- closureConvert t1 bounds
    ir2 <- closureConvert t2 bounds
    return $ IrLet dummyName IrClo ir1 (IrCall (IrAccess (IrVar dummyName) IrFunTy 0) [IrVar dummyName,ir2] (convertType ty))
    -- return $ IrCall ir1 [ir2] IrInt
  Print _ str tm -> do
      ir1 <- closureConvert tm bounds
      return $ IrPrint str ir1
  BinaryOp _ op t1 t2 -> do
    ir1 <- closureConvert t1 bounds
    ir2 <- closureConvert t2 bounds
    return $ IrBinaryOp op ir1 ir2
  Fix _ fn ty str ty' (Sc2 tm) -> do
    let (names, tm') = cfreshen2 bounds (convertType ty, fn) (convertType ty', str) tm -- Libero un nuevo nombre
        fn' = "_" ++ (snd . head) names               -- Nombre nuevo para la funcion
        varLibres = map IrVar (freeVars tm')  -- Lista de valiables libres
        cloName = "_" ++ fn'                  -- Nombre de la closure
    body <- closureConvert tm' names
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
    let (bounds', t2') = cfreshen bounds (convertType ty, name) t2
    ir2 <- closureConvert t2' bounds'
    return $ IrLet ((snd . head) bounds') (convertType ty) ir1 ir2

cfreshen :: [TyName] -> TyName -> TTerm -> ([TyName], TTerm)
cfreshen ns (ty,n) tm = let newName = "_" ++ freshen (map snd ns) n
                            newTree = open newName (Sc1 tm)
                        in ((ty,newName):ns, newTree)

cfreshen2 :: [TyName] -> TyName -> TyName -> TTerm -> ([TyName], TTerm)
cfreshen2 ns (ty1, n1) (ty2, n2) tm =
  let ns' = map snd ns
      name1 = "_" ++ freshen ns' n1
      name2 = "_" ++ freshen (name1:ns') n2
      newNames = (ty1, name1):(ty2,name2):ns
      newTree = open2 name1 name2 (Sc2 tm)
  in (newNames, newTree)

-- runCC :: Module -> IrDecls
-- runCC [] = IrDecls []
-- runCC m = let (_, decls) = runWriter $ runStateT  (runCC' m)
--           in IrDecls decls

runCC :: [Decl TTerm] -> IrDecls
runCC m = let mon = runCC' m
          in IrDecls $ (snd . runWriter . runStateT mon) 0

-- closureConvertModule :: Module -> CCState
runCC' :: Module -> CCState ()
runCC' [Decl _ name ty t] = do
  r <- closureConvert t []
  tell [IrVal name (convertType ty) r]
  return ()
runCC'((Decl _ name ty t):ms) = do
  r <- closureConvert t []
  tell [IrVal name (convertType ty) r]
  runCC' ms
runCC' _ = error "No se puede convertir"

convertType :: Ty -> IrTy
convertType NatTy = IrInt
convertType (FunTy _ _) = IrClo
