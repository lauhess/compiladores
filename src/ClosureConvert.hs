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
  -- Lam (_, FunTy _ ty) fn tyVar (Sc1 tm) -> do
  t@(Lam i n ty body@(Sc1 b)) -> do
    nombreFuncion <- varName "f"
    nombreArg <- varName n
    let body' = open nombreArg body -- se llama al argumento dentro de body donde antes había (Bound 0)
    body'' <- closureConvert body'

    let fv = freeVarsTy b

    closure <- varName (nombreFuncion ++ "clos")

    -- cuerpo va a tener las variables libres igualadas a alguna posición del entorno de la clausura
    -- y finalmente body''
    let cuerpo = args2vars fv body'' closure
    let tipoRetorno = ty2IrTy ty

    let decl = IrFun nombreFuncion tipoRetorno [(closure, IrClo), (nombreArg, IrInt)] cuerpo
    tell [decl]

    return $ MkClosure nombreFuncion $ map (IrVar . fst) fv
  Lam {} -> error "Lam: Tipo invalido"
  App (_,ty) t1 t2 -> do
    dummyName <- cfreshenName "App"
    ir1 <- closureConvert t1
    ir2 <- closureConvert t2
    -- trace ("===> " ++ dummyName ++ show ty) $ return ()
    return $ IrLet dummyName IrClo ir1 (IrCall (IrAccess (IrVar dummyName) IrFunTy 0) [IrVar dummyName,ir2] (convertType ty))
    -- return $ IrCall ir1 [ir2] IrInt
  Print _ str tm -> do
      ir1 <- closureConvert tm
      return $ IrPrint str ir1
  BinaryOp _ op t1 t2 -> do
    ir1 <- closureConvert t1
    ir2 <- closureConvert t2
    return $ IrBinaryOp op ir1 ir2
  -- Fix (_, FunTy _ ty) fn ty1 x ty2 (Sc2 tm) -> do
  t@(Fix i fn fty vn vty body@(Sc2 b)) -> do
    nombreFuncion <- varName ("fix_" ++ fn)
    nombreArg <- varName vn
    closure <- varName (nombreFuncion ++ "clos")
    let body' = open2 closure nombreArg body
    body'' <- closureConvert body'

    let fv = freeVarsTy b

    let cuerpo = args2vars fv body'' closure
    let tipoRetorno = ty2IrTy fty

    let decl = IrFun nombreFuncion tipoRetorno [(closure, IrClo), (nombreArg, IrInt)] cuerpo
    tell [decl]

    return $ MkClosure nombreFuncion $ map (IrVar . fst) fv
  Fix {} -> error "Fix: Tipo invalido"
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

varName :: Name -> CCState Name
varName prefix = do
    (n, ns) <- get
    put (n+1, ns)
    return (prefix ++ "_" ++  show n)

args2vars :: [(Name, Ty)] -> Ir -> Name -> Ir
args2vars fv t closure =
    foldr   (\((v, ty), i) ir -> IrLet v (ty2IrTy ty) (IrAccess (IrVar closure) (ty2IrTy ty) i) ir)
            t
            (zip fv [1..])

var2ir :: Var -> Ir
var2ir (Free name) = IrVar name
var2ir (Global name)  = IrGlobal name
var2ir (Bound _) = undefined

ty2IrTy :: Ty -> IrTy
ty2IrTy NatTy = IrInt
ty2IrTy (FunTy _ _) = IrFunTy

