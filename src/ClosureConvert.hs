module ClosureConvert where

import Lang
import IR
import Control.Monad.State (StateT (StateT, runStateT), MonadState (get))
import Control.Monad.Writer (Writer, MonadWriter (writer), runWriter)
import PPrint (freshen)

term2ir :: TTerm -> Ir
term2ir = undefined

ty2irTy :: Ty -> IrTy
ty2irTy = undefined

decl2irDecl :: Decl TTerm -> IrDecl
decl2irDecl (Decl _ name NatTy t) = IrVal name IrInt (term2ir t)
decl2irDecl (Decl _ name (FunTy declTy retTy) t) = IrFun name (head $ ty2irTy retTy) (ty2irTy declTy) (term2ir t)

closureConvert :: TTerm -> [Name] -> StateT Int (Writer [IrDecl]) Ir
closureConvert t bounds = case t of
  V _ (Bound n) -> mkWS (IrVar (bounds !! n)) 0 []
  V _ (Free n) -> mkWS (IrVar n) 0 []
  V _ (Global n) -> mkWS (IrGlobal n) 0 []
  Const _ co@(CNat n) ->
    mkWS (IrConst co) 0 []
  Lam _ fn ty (Sc1 tm) -> 
    let bounds'@(name':_) = (cfreshen bounds fn:bounds)
        fn' = "_" ++ name'
        ((ir, s'), irds) = runWS tm 0 bounds'
    in mkWS (MkClosure fn' (map IrVar bounds')) s' irds
  App _ tm tm' -> _
  Print _ str tm ->
    let ((ir1, s1), irds) = runWS tm 0 bounds
     in mkWS (IrPrint str ir1) s1 irds
  BinaryOp _ op t1 t2 ->
    let ((ir1, s1), irds) = runWS t1 0 bounds -- ToDo: Check
        ((ir2, s2), irds') = runWS t2 s1 bounds
        ir = IrBinaryOp op ir1 ir2
    in mkWS ir s2 (irds ++ irds')
  Fix _ s ty str ty' sc -> _
  IfZ _ tm tm' tm2 -> _
  Let _ name ty t1 (Sc1 t2) -> 
    let ((ir1, s1), irds) = runWS t1 0 bounds
        ((ir2, s2), irds') = runWS t2 s1 (cfreshen bounds name:bounds)
     in mkWS (IrLet name (ty2irTy ty) ir1 ir2) s2 (irds ++ irds')


runCC :: Module -> [IrDecl]
runCC = undefined

runWS :: TTerm -> Int -> [Name] -> ((Ir, Int), [IrDecl])
runWS t s bounds = runWriter $ runStateT (closureConvert t bounds) s

mkWS :: Ir -> Int -> [IrDecl] -> StateT Int (Writer [IrDecl]) Ir
mkWS ir s irds = StateT (\s' -> writer ((ir, s + s'), irds))

cfreshen :: [Name] -> Name -> Name
cfreshen ns n = "_" ++ freshen ns n