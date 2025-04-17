{-# LANGUAGE LambdaCase #-}
module Optimization where
import Lang
import Eval (semOp)
import Subst
import MonadFD4 (MonadFD4, lookupDecl, printFD4, getProf, clearFD4, addDecl)
import Data.Foldable (foldrM)
import Control.Monad (when)
import Data.Function (on)

iterations :: Int
iterations = 4

os :: MonadFD4 m => [TTerm -> m TTerm]
os = [constantFolding, deadCodeElimination, constantPropagation, inlineExpansion]

manyApp :: MonadFD4 m => (Decl TTerm -> m (Decl TTerm)) -> Int -> [Decl TTerm] -> m [Decl TTerm]
manyApp f 0 xs = do
  prof <- getProf
  when prof $ printFD4 $ "Se realizaron "++ show iterations ++ " iteraciones de optimizacion"
  return xs
manyApp f n xs = do
  xs' <- mapM f xs
  let notEqual = filter (not . uncurry (compTTerm `on` declBody)) $ zip xs xs'
  if null notEqual
    then do
      prof <- getProf
      when prof $ printFD4 $ "Se realizaron "++ show (iterations - n) ++ " iteraciones de optimizacion"
      return xs'
    else manyApp f (n-1) xs'

optDecls :: MonadFD4 m => [Decl TTerm] -> m [Decl TTerm]
optDecls [] = return []
optDecls ds = do
  prof <- getProf
  when prof $ printFD4 "Iniciando optimización de términos"
  dsOpt <- manyApp optDecls' iterations ds
  let names   = map declName dsOpt
      dsOpt'  = dead names dsOpt
      dsOpt'' = filter (\d -> declName d `notElem` dsOpt') dsOpt
  when prof $ printFD4 "Eliminando código muerto"
  clearFD4
  dsOpt''' <- mapM addDecl dsOpt''
  return dsOpt


dead :: [Name] -> [Decl TTerm] -> [Name]
dead = foldr dead'

dead' :: Decl TTerm -> [Name] -> [Name]
dead' _ [] = []
dead' (Decl _ _ _ t') names' = go names' t'
  where
    go :: [Name] -> TTerm -> [Name]
    go [] _ = []
    go names t = case t of
      V _ (Global name) -> filter (/= name) names
      V _ (Free name)   -> filter (/= name) names
      V _ _             -> names
      Const _ _         -> names
      Lam _ s ty (Sc1 t1) -> go names t1
      App _ t1 t2       -> go (go names t1) t2
      Print _ s t1      -> go names t1
      BinaryOp _ op t1 t2 -> go (go names t1) t2
      Fix _ s ty str ty' (Sc2 t1) -> go names t1
      IfZ _ c t1 t2     -> go (go (go names c) t1) t2
      Let _ s ty t1 (Sc1 t2) -> go (go names t1) t2

optDecls'  :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optDecls' (Decl i name ty t) = optimizeTerm t >>= \t'-> return $ Decl i name ty t'


optimizeTerm :: MonadFD4 m => TTerm -> m TTerm
optimizeTerm t = do
  prof <- getProf
  foldrM ($) t os
  -- return $ Decl i name ty t'
  -- go prof t 0 
-- >>= \t' -> 
  -- printFD4 (show t') >> 
  -- return t'
    -- where
    --     go :: MonadFD4 m => Bool -> TTerm -> Int -> m TTerm
    --     go prof tm i = do 
    --       ft <- foldrM ($) tm os
    --       if compTTerm t ft || i >= iterations
    --         then (if prof 
    --           then printFD4 ("\tSe hicieron " ++ show i ++ " iteraciones de optimizacion") >> pp ft >>= printFD4 >> return ft 
    --           else return ft)
    --         else go prof ft (i+1)


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
  Let i s ty t1 s1@(Sc1 t2) -> case t1 of
    (Const _ (CNat n)) -> return $ subst t1 s1
    _                  -> constantPropagation t1 >>= \t1' ->
                          constantPropagation t2  >>= \t2'  ->
                          return $ Let i s ty t1' (Sc1 t2')

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
    (Const _ (CNat n)) -> if n == 0 then t1 else t2
    _                  -> t
  Let i s ty t1 (Sc1 t2) -> do
    b1 <- isImpure t1
    if boundUse t2 || b1
    then deadCodeElimination t1 >>= \t1' ->
          deadCodeElimination t2 >>= \t2' ->
          return $ Let i s ty t1' (Sc1 t2')
    else return $ reBound t2
    where reBound = varChanger 0 (\_ p n -> V p (Free n)) (\d p ix -> if ix > d then V p (Bound (ix - 1)) else V p (Bound ix))


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
  BinaryOp i Add (Const _ (CNat 0)) var -> return var
  BinaryOp i Add var (Const _ (CNat 0)) -> return var
  BinaryOp i Sub var (Const _ (CNat 0)) -> return var
  BinaryOp i Sub izq@(Const _ (CNat 0)) var ->
    isPure var >>= \case   -- Solo optimizamos si la variable es pura 
    True -> return izq
    False -> do
      var' <- constantFolding var
      return $ BinaryOp i Sub izq var'
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
  V i (Global name) -> do
    var <- lookupDecl name
    case var of
      (Just term) -> 
        isPure term >>= \b1 ->
        if b1 
           then return term 
           else return t
      _           -> return t
  V i var -> return t
  Const i co -> return t
  Lam i s ty (Sc1 t1) -> inlineExpansion t1 >>= \t1' ->
                         return $ Lam i s ty (Sc1 t1')
  App i (Lam _ _ _ t1) c@(Const _ _) -> return $ subst c t1
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

isPure :: MonadFD4 m => TTerm -> m Bool
isPure (V p (Global var)) = lookupDecl var >>= \case
  Just t' -> isPure t'
  Nothing -> return False
isPure (V p _) = return True
isPure (Lam p y ty (Sc1 t))   = isPure t
isPure (App p l r)   = do
  b1 <- isPure l 
  b2 <- isPure r
  return $ b1 && b2
isPure (Fix p f fty x xty (Sc2 t)) = isPure t
isPure (IfZ p c t e) = do 
  b1 <- isPure c
  b2 <- isPure t
  b3 <- isPure e
  return $ b1 && b2 && b3
isPure t@(Const _ _) = return True
isPure (Print p str t) = return False
isPure (BinaryOp p op t u) = do
  b1 <- isPure t
  b2 <- isPure u
  return $ b1 && b2
isPure (Let p v vty m (Sc1 o)) = do
  b1 <- isPure m 
  b2 <- isPure o
  return $ b1 && b2

isImpure :: MonadFD4 m => TTerm -> m Bool
isImpure t = isPure t >>= \b -> return $ not b