module ClosureConvert where

import Lang
import IR
import Control.Monad.Writer (Writer, MonadWriter (tell), runWriter)
import MonadFD4
import Subst
import Debug.Trace

type CCState a = StateT (Int, [(Name,IrTy)]) (Writer [IrDecl]) a

type TyName = (IrTy, Name)

-- term2ir :: TTerm -> Ir
-- term2ir = undefined

-- ty2irTy :: Ty -> IrTy
-- ty2irTy = undefined

-- decl2irDecl :: Decl TTerm -> IrDecl
-- decl2irDecl (Decl _ name NatTy t) = IrVal name IrInt (term2ir t)
-- decl2irDecl (Decl _ name (FunTy declTy retTy) t) = IrFun name (head $ ty2irTy retTy) (ty2irTy declTy) (term2ir t)

closureConvert :: TTerm -> CCState Ir
closureConvert t = case t of
  V _ (Bound n) -> error "Falto consumir alguna lambda"
  V _ (Free n) -> return $ IrVar n
  V _ (Global n) -> return $ IrGlobal n
  Const _ co@(CNat n) -> return $ IrConst co
  Lam (_, (FunTy _ ty)) fn tyVar (Sc1 tm) -> do
    (tm', varName) <- cfreshen fn (convertType tyVar) tm -- Libero un nuevo nombre
    let varLibres = map IrVar (freeVars tm) -- Lista de valiables libres
    cloName <- cfreshenName fn                 -- Nombre de la closure
    fn' <- cfreshenName fn                     -- Nombre de la función
    bounds <- getFreeVars' tm
    body <- closureConvert tm'
    bounds' <- getFreeVars' tm'
    let bodyBoundingVars = foldr (\(i, (name, ty')) body'  ->
         IrLet name ty' (IrAccess (IrVar cloName) IrInt i) body')
          body
          (zip [1..] (reverse bounds))
    tell [IrFun fn' (convertType ty) ((cloName, IrClo):bounds') bodyBoundingVars]
    trace ("-> En: " ++ fn ++ "\n\tvarName: " ++ varName ++ "\n\tCloName: " ++ cloName ++ "\n\t ListaBounds: " ++ (show bounds) ++ "\n\t ListaBounds': " ++ (show bounds')) $ return ()
    return $ MkClosure fn' varLibres
  App (_,ty) t1 t2 -> do
    dummyName <- cfreshenName "App"
    ir1 <- closureConvert t1
    ir2 <- closureConvert t2
    trace ("===> " ++ dummyName ++ show ty) $ return ()
    return $ IrLet dummyName IrClo ir1 (IrCall (IrAccess (IrVar dummyName) IrFunTy 0) [IrVar dummyName,ir2] (convertType ty))
    -- return $ IrCall ir1 [ir2] IrInt
  Print _ str tm -> do
      ir1 <- closureConvert tm
      return $ IrPrint str ir1
  BinaryOp _ op t1 t2 -> do
    ir1 <- closureConvert t1
    ir2 <- closureConvert t2
    return $ IrBinaryOp op ir1 ir2
  Fix _ fn ty str ty' (Sc2 tm) -> do
    (tm', fn', cloName) <- cfreshen2 fn (convertType ty) str (convertType ty') tm -- Libero un nuevo nombre
    let varLibres = map IrVar (freeVars tm')  -- Lista de valiables libres
    body <- closureConvert tm'
    -- tell _
    let bodyBoundingVars = foldr (\(i, IrVar name) body'  ->
         IrLet name IrInt (IrAccess (IrVar cloName) IrInt i) body')
          body
          (zip [1..] varLibres)
    tell [IrFun cloName IrClo [(fn', IrInt)] bodyBoundingVars]
    return $ MkClosure fn' varLibres
  IfZ _ t1 t2 t3 -> do
    ir1 <- closureConvert t1 
    ir2 <- closureConvert t2 
    ir3 <- closureConvert t3 
    return $ IrIfZ ir1 ir2 ir3
  Let _ name ty t1 (Sc1 t2) -> do
    ir1 <- closureConvert t1
    (t2', name') <- cfreshen name (convertType ty) t2
    ir2 <- closureConvert t2'
    return $ IrLet name' (convertType ty) ir1 ir2

cfreshenName :: Name -> CCState Name
cfreshenName name = do
  (i, ns) <- get
  let newName = "_" ++ show i ++ name ++ "_"
  put (i+1, ns)
  return newName

cfreshen :: Name -> IrTy -> TTerm -> CCState (TTerm, Name)
cfreshen name ty tm = do 
  (i, ns) <- get
  let newName = "_" ++ show i ++ name ++ "_"
  put (i+1, (newName, ty):ns)
  return (open newName (Sc1 tm), newName)

cfreshen2 :: Name -> IrTy -> Name -> IrTy -> TTerm -> CCState (TTerm, Name, Name)
cfreshen2 n1 ty1 n2 ty2 tm = do
  (i, ns) <- get
  let newName1 = "_" ++ show i ++ n1 ++ "_"
      newName2 = "_" ++ show (i + 1) ++ n1 ++ "_"
  put (i+2, (newName1,ty1):(newName2, ty2):ns)
  return (open2 newName1 newName2 (Sc2 tm), newName1, newName2)

runCC :: [Decl TTerm] -> IrDecls
runCC m = let mon = runCC' m
          in IrDecls $ (snd . runWriter . runStateT mon) (0,[])

-- closureConvertModule :: Module -> CCState
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
convertType NatTy = IrInt
convertType (FunTy _ _) = IrClo

getFreeVars' :: TTerm -> CCState [(Name, IrTy)]
getFreeVars' t = do
  (i, ns) <- get
  let libres = freeVars t
  return $ filter (\(n,_) -> n `elem` libres) ns