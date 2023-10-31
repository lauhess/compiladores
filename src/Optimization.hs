{-# LANGUAGE LambdaCase #-}
module Optimization where
import Lang
import Eval (semOp)
import Subst
import MonadFD4 (MonadFD4, lookupDecl, printFD4)
import Data.Foldable (foldrM)
import Debug.Trace
import PPrint

iterations :: Int
iterations = 4

os :: MonadFD4 m => [TTerm -> m TTerm]
os = [constantFolding, deadCodeElimination, constantPropagation]

optimizeTerm :: MonadFD4 m => TTerm -> m TTerm
optimizeTerm t = go t 0 >>= \t' -> 
  -- printFD4 (show t') >> 
  return t'
    where
        go :: MonadFD4 m => TTerm -> Int -> m TTerm
        go tm i = do 
          ft <- foldrM (\f tm' -> f tm') tm os
          t''' <- pp ft
          printFD4 t'''
          if compTTerm t ft || i >= iterations
            then printFD4 ("\tSe hicieron " ++ show i ++ " iteraciones de optimizacion") >> 
                 return ft 
            else go ft (i+1)
        

constantPropagation :: MonadFD4 m => TTerm -> m TTerm
constantPropagation t = case t of
  V i var -> return t
  Const i co -> return t
  Lam i s ty (Sc1 t1) -> constantPropagation t1 >>= \t1' -> 
                         return $ Lam i s ty (Sc1 t1')
  App i t1 t2 -> constantPropagation t1 >>= \t1' ->
                 constantPropagation t2 >>= \t2' -> 
                 return $ App i t1' t2'
  Print i s t1 -> constantPropagation t1 >>= \t1' ->
                  return $ Print i s t1'
  BinaryOp i bo t1 t2 -> constantPropagation t1 >>= \t1' ->
                         constantPropagation t2 >>= \t2' ->
                         return $ BinaryOp i bo t1' t2'
  Fix i s ty str ty' (Sc2 t1) -> constantPropagation t1 >>= \t1' ->
                                 return $ Fix i s ty str ty' (Sc2 t1')
  IfZ i c t1 t2 -> constantPropagation c >>= \c' ->
                   constantPropagation t1 >>= \t1' ->
                   constantPropagation t2 >>= \t2' ->
                   return $ IfZ i c' t1' t2'
  Let i s ty t1 s1@(Sc1 t2) -> return $ case t1 of
    (Const _ (CNat n)) -> subst t1 s1
    _                  -> t

deadCodeElimination :: MonadFD4 m => TTerm -> m TTerm
deadCodeElimination t = case t of
  V i (Global var) -> lookupDecl var >>= \case
    Just n@(Const _ (CNat _)) ->  return n
    _ -> return t
  V i var -> return t
  Const i co -> return t
  Lam i s ty (Sc1 t1) -> deadCodeElimination t1 >>= \t1' ->
                         return $ Lam i s ty (Sc1 t1')
  App i t1 t2 -> deadCodeElimination t1 >>= \t1' ->
                 deadCodeElimination t2 >>= \t2' ->
                 return $ App i t1' t2'
  Print i s t1 -> deadCodeElimination t1 >>= \t1' ->
                  return $ Print i s t1'
  BinaryOp i bo t1 t2 -> deadCodeElimination t1 >>= \t1' ->
                         deadCodeElimination t2 >>= \t2' ->
                         return $ BinaryOp i bo t1' t2'
  Fix i s ty str ty' (Sc2 t1) -> deadCodeElimination t1 >>= \t1' ->
                                 return $ Fix i s ty str ty' (Sc2 t1')
  IfZ i c t1 t2 -> return $ case c of
    (Const _ (CNat n)) -> if n == 0 then t2 else t1
    _                  -> t
  Let i s ty t1 (Sc1 t2) -> if True -- boundUse t2 || isImpure t1
                            then deadCodeElimination t1 >>= \t1' ->
                                 deadCodeElimination t2 >>= \t2' ->
                                 return $ Let i s ty t1' (Sc1 t2')
                            else return $ reBound t2
                            where reBound = varChanger (\_ p n -> V p (Free n)) (\d p ix -> if ix > d then V p (Bound (ix - 1)) else V p (Bound ix))


constantFolding :: MonadFD4 m => TTerm -> m TTerm
constantFolding t = case t of
  V i var -> return t
  Const i co -> return t
  Lam i s ty (Sc1 t1) -> constantFolding t1 >>= \t1' ->
                         return $ Lam i s ty (Sc1 t1')
  App i t1 t2 -> constantFolding t1 >>= \t1' ->
                 constantFolding t2 >>= \t2' ->
                 return $ App i t1' t2'
  Print i s t1 -> constantFolding t1 >>= \t1' ->
                  return $ Print i s t1'
  BinaryOp i bo (Const _ (CNat n)) (Const _ (CNat m)) -> return $ Const i (CNat (semOp bo n m))
  BinaryOp i bo t1 t2 -> constantFolding t1 >>= \t1' ->
                         constantFolding t2 >>= \t2' ->
                         return $ BinaryOp i bo t1' t2'
  Fix i s ty str ty' (Sc2 t1) -> constantFolding t1 >>= \t1' ->
                                 return $ Fix i s ty str ty' (Sc2 t1')
  IfZ i c t1 t2 -> constantFolding c >>= \c' ->
                   constantFolding t1 >>= \t1' ->
                   constantFolding t2 >>= \t2' ->
                   return $ IfZ i c' t1' t2'
  Let i s ty t1 (Sc1 t2) -> constantFolding t1 >>= \t1' ->
                            constantFolding t2 >>= \t2' ->
                            return $ Let i s ty t1' (Sc1 t2')

inlineExpansion ::MonadFD4 m => TTerm -> m TTerm
inlineExpansion t = case t of
  V i var -> return t
  Const i co -> return t
  Lam i s ty (Sc1 t1) -> inlineExpansion t1 >>= \t1' ->
                         return $ Lam i s ty (Sc1 t1')
  App i t1 t2 -> inlineExpansion t1 >>= \t1' ->
                 inlineExpansion t2 >>= \t2' ->
                 return $ App i t1' t2'
  Print i s t1 -> inlineExpansion t1 >>= \t1' ->
                  return $ Print i s t1'
  BinaryOp i bo t1 t2 -> inlineExpansion t1 >>= \t1' ->
                         inlineExpansion t2 >>= \t2' ->
                         return $ BinaryOp i bo t1' t2'
  Fix i s ty str ty' (Sc2 t1) -> inlineExpansion t1 >>= \t1' ->
                                 return $ Fix i s ty str ty' (Sc2 t1')
  IfZ i c t1 t2 -> inlineExpansion c >>= \c' ->
                   inlineExpansion t1 >>= \t1' ->
                   inlineExpansion t2 >>= \t2' ->
                   return $ IfZ i c' t1' t2'
  Let i s ty t1 (Sc1 t2) -> inlineExpansion t1 >>= \t1' ->
                            inlineExpansion t2 >>= \t2' ->
                            return $ Let i s ty t1' (Sc1 t2')

-- Compare terms and returns True if they are equal
-- Ignore info and positions and names
compTTerm :: TTerm -> TTerm -> Bool
compTTerm (V _ x) (V _ y) = x == y
compTTerm (Const _ c1) (Const _ c2) = c1 == c2
compTTerm (Lam _ _ ty1 (Sc1 t1)) (Lam _ _ ty2 (Sc1 t2)) =
  ty1 == ty2 && compTTerm t1 t2
compTTerm (App _ t1 t2) (App _ t1' t2') =
  compTTerm t1 t1' && compTTerm t2 t2'
compTTerm (Print _ s1 t1) (Print _ s2 t2) =
  s1 == s2 && compTTerm t1 t2
compTTerm (BinaryOp _ op1 t1 t2) (BinaryOp _ op2 t1' t2') =
  op1 == op2 && compTTerm t1 t1' && compTTerm t2 t2'
compTTerm (Fix _ _ ty1 _ ty2 (Sc2 t1)) (Fix _ _ ty3 _ ty4 (Sc2 t2)) =
  ty1 == ty3 && ty2 == ty4 && compTTerm t1 t2
compTTerm (IfZ _ t1 t2 t3) (IfZ _ t1' t2' t3') =
  compTTerm t1 t1' && compTTerm t2 t2' && compTTerm t3 t3'
compTTerm (Let _ _ ty1 t11 (Sc1 t12)) (Let _ _ ty2 t21 (Sc1 t22)) =
  ty1 == ty2 && compTTerm t11 t21 && compTTerm t12 t22
compTTerm _ _ = False


isPure :: TTerm -> Bool
isPure (V p (Global _)) = False
isPure (V p _) = True
isPure (Lam p y ty (Sc1 t))   = isPure t
isPure (App p l r)   = isPure l && isPure r
isPure (Fix p f fty x xty (Sc2 t)) = isPure t
isPure (IfZ p c t e) = isPure c && isPure t && isPure e
isPure t@(Const _ _) = True
isPure (Print p str t) = False
isPure (BinaryOp p op t u) = isPure t && isPure u
isPure (Let p v vty m (Sc1 o)) = isPure o

isImpure :: TTerm -> Bool
isImpure t = not (isPure t)