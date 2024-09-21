{-# LANGUAGE LambdaCase #-}
module CEK where
import Lang
import Global
import MonadFD4 ( MonadFD4, lookupDecl, failFD4, modify, getProf, gets, printFD4 )
import Eval (semOp)
import Common (Pos(..))
import Subst (varChanger)

data Frame =
    AppEval CEKEnv TTerm
    | Clos Val
    | IfZEval CEKEnv TTerm TTerm
    | OpLeftEval BinaryOp CEKEnv TTerm
    | OpRightEval BinaryOp Val
    | PrintEval String
    deriving Show

type Kont = [Frame]

data Val =
      Vall Int
    | ClosFun [Val] Name Ty TTerm
    | ClosFix [Val] Name Ty Name Ty TTerm
    deriving Show

type CEKEnv = [Val]


-- Agregá un marco a la continuación y descendiendo por el término a ejecutar
seek    :: MonadFD4 m => TTerm -> m Val
seek term = inicializarStats >> seek' term [] []

seek'    :: MonadFD4 m => TTerm -> CEKEnv -> Kont -> m Val
seek' term p k = incTranCount >> case term of
    (Print _ s tm)      -> seek' tm p $ PrintEval s : k
    (BinaryOp _ op t u) -> seek' t p $ OpLeftEval op p u : k
    (IfZ _ c t u)       -> seek' c p $ IfZEval p t u : k
    (App _ t u)         -> seek' t p $ AppEval p u : k
    (V _ (Bound n))     -> destroy (p !! n) k
    (V i (Global name)) -> lookupDecl name >>= \case
        (Just t) -> seek' t p k
        Nothing  -> failFD4 $ "Variable global " ++ name ++ " no encontrada."
    (V _ _)             -> failFD4 "seek' no esperaba variables libres"
    (Const _ (CNat n))  -> destroy (Vall n) k
    (Lam _ n ty (Sc1 t)) ->   destroy (ClosFun p n ty t) k
    (Fix _ n1 ty1 n2 ty2 (Sc2 t)) -> destroy (ClosFix p n1 ty1 n2 ty2 t) k
    (Let info n ty s (Sc1 t))   -> seek' (App info (Lam info n ty (Sc1 t)) s) p k

-- Da valor a una continuación << >>
destroy :: MonadFD4 m => Val          -> Kont -> m Val
destroy var kont = incTranCount >> go var kont
    where
        go v@(Vall n) ((PrintEval s):ks) = printFD4 (s ++ show n) >> destroy v ks
        go v ((OpLeftEval op p t):ks) = seek' t p $ OpRightEval op v:ks
        go (Vall n') ((OpRightEval op (Vall n)):ks) = destroy (Vall (semOp op n n')) ks
        go (Vall 0) ((IfZEval p t1 _):ks) = seek' t1 p ks
        go (Vall n) ((IfZEval p _ t2):ks) = seek' t2 p ks
        go v ((AppEval p t):ks) = seek' t p (Clos v:ks)
        go v ((Clos val):ks) = incClosCount >> case val of
            (ClosFun p _ _ t)     -> seek' t (v:p) ks
            (ClosFix p _ _ _ _ t) -> seek' t (v:val:p) ks
            _                     -> failFD4 "Destroy esperaba clausura y recibio Vall"
        go v [] = return v
        go v ks = failFD4 $ "Destroy: valor no contemplado \n\t" ++ show v ++ "\n\t" ++ show (head ks)

val2term :: Val -> TTerm
val2term val = case val of
  Vall n -> Const (NoPos, NatTy "") (CNat n)
  ClosFun vs n ty t -> 
    let c = go vs (length vs) t
    in Lam (NoPos, FunTy "" ty (getTy t)) n ty $ Sc1 c
  ClosFix vs n1 ty1 n2 ty2 t -> 
    let c = go vs (length vs) t
    in Fix (NoPos, ty1) n1 ty1 n2 ty2 $ Sc2 c
  where
    go [] _ term = term
    go (v:vs') m term = go vs' (m - 1) (subst' m (val2term v) (Sc1 term))

subst' :: Int -> Tm info Var -> Scope info Var -> Tm info Var
subst' k n (Sc1 m) = varChanger k (\_ p n' -> V p (Free n')) bnd m
   where bnd depth p i
             | i == depth = n
             | otherwise  = V p (Bound i)

inicializarStats :: MonadFD4 m => m ()
inicializarStats = getProf >>= \case
  True -> modify (\s -> s {
    statistics = StatsCEK 0 0
  })
  _ -> modify (\s -> s {
    statistics = Dummy
  })

incTranCount :: MonadFD4 m => m ()
incTranCount = gets statistics >>= \case
  (StatsCEK t c) -> modify (\s -> s {
      statistics = StatsCEK (t + 1) c
    })
  StatsBytecode {} -> failFD4 "Tipo de estadistica equivocado"
  _ -> return ()

incClosCount :: MonadFD4 m => m ()
incClosCount = gets statistics >>= \case
  (StatsCEK t c) -> modify (\s -> s {
      statistics = StatsCEK t (c + 1)
    })
  StatsBytecode {} -> failFD4 "Tipo de estadistica equivocado"
  _ -> return ()