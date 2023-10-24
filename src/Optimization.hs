module Optimization where
import Lang
import Eval (semOp)
import Subst

iterations :: Int
iterations = 100

optimizeTerm :: TTerm -> TTerm
optimizeTerm = go False 0
    where
        os = [constantFolding, deadCodeElimination, constantPropagation]
        go c i t
            | c || i >= iterations = t
            | otherwise = let t' = foldr (\f tm -> f tm) t os
                        in go (compTTerm t t') (i+1) t'

constantPropagation :: TTerm -> TTerm
constantPropagation t = case t of
  V i var -> t
  Const i co -> t
  Lam i s ty (Sc1 t1) -> let t1' = constantPropagation t1
                          in Lam i s ty (Sc1 t1')
  App i t1 t2 -> let t1' = constantPropagation t1
                     t2' = constantPropagation t2
                   in App i t1' t2'
  Print i s t1 -> let t1' = constantPropagation t1
                   in Print i s t1'
  BinaryOp i bo t1 t2 -> let t1' = constantPropagation t1
                             t2' = constantPropagation t2
                          in BinaryOp i bo t1' t2'
  Fix i s ty str ty' (Sc2 t1) -> let t1' = constantPropagation t1
                                  in Fix i s ty str ty' (Sc2 t1')
  IfZ i c t1 t2 -> let c' = constantPropagation c
                       t1' = constantPropagation t1
                       t2' = constantPropagation t2
                    in IfZ i c' t1' t2'
  Let i s ty t1 s1@(Sc1 t2) -> case t1 of
    (Const _ (CNat n)) -> subst t1 s1
    _                  -> t

deadCodeElimination :: TTerm -> TTerm
deadCodeElimination t = case t of
  V i var -> t
  Const i co -> t
  Lam i s ty (Sc1 t1) -> let t1' = deadCodeElimination t1
                          in Lam i s ty (Sc1 t1')
  App i t1 t2 -> let t1' = deadCodeElimination t1
                     t2' = deadCodeElimination t2
                   in App i t1' t2'
  Print i s t1 -> let t1' = deadCodeElimination t1
                   in Print i s t1'
  BinaryOp i bo t1 t2 -> let t1' = deadCodeElimination t1
                             t2' = deadCodeElimination t2
                          in BinaryOp i bo t1' t2'
  Fix i s ty str ty' (Sc2 t1) -> let t1' = deadCodeElimination t1
                                  in Fix i s ty str ty' (Sc2 t1')
  IfZ i c t1 t2 -> case c of
    (Const _ (CNat n)) -> if n == 0 then t2 else t1
    _                  -> t
  Let i s ty t1 (Sc1 t2) -> let t1' = deadCodeElimination t1
                                t2' = deadCodeElimination t2
                             in Let i s ty t1' (Sc1 t2')


constantFolding :: TTerm -> TTerm
constantFolding t = case t of
  V i var -> t
  Const i co -> t
  Lam i s ty (Sc1 t1) -> let t1' = constantFolding t1
                          in Lam i s ty (Sc1 t1')
  App i t1 t2 -> let t1' = constantFolding t1
                     t2' = constantFolding t2
                   in App i t1' t2'
  Print i s t1 -> let t1' = constantFolding t1
                   in Print i s t1'
  BinaryOp i bo (Const _ (CNat n)) (Const _ (CNat m)) -> Const i (CNat (semOp bo n m))
  BinaryOp i bo t1 t2 -> let t1' = constantFolding t1
                             t2' = constantFolding t2
                          in BinaryOp i bo t1' t2'
  Fix i s ty str ty' (Sc2 t1) -> let t1' = constantFolding t1
                                  in Fix i s ty str ty' (Sc2 t1')
  IfZ i c t1 t2 -> let t1' = constantFolding c
                       t2' = constantFolding t1
                       t3' = constantFolding t2
                    in IfZ i t1' t2' t3'
  Let i s ty t1 (Sc1 t2) -> let t1' = constantFolding t1
                                t2' = constantFolding t2
                             in Let i s ty t1' (Sc1 t2')

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


