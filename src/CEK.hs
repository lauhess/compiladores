{-# LANGUAGE LambdaCase #-}
module CEK where
import Lang
import MonadFD4 ( MonadFD4, lookupDecl, failFD4 )
import Eval (semOp)
import Common (Pos(..))
import Debug.Trace

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

seek    :: MonadFD4 m => TTerm -> CEKEnv -> Kont -> m Val
seek term p k = case term of
    (Print _ s tm)      -> seek tm p $ PrintEval s : k
    (BinaryOp _ op t u) -> seek t p $ OpLeftEval op p u : k
    (IfZ _ c t u)       -> seek c p $ IfZEval p t u : k
    (App _ t u)         -> seek t p $ AppEval p u : k
    (V _ (Bound n))     -> destroy (p !! n) k
    (V i (Global name)) -> lookupDecl name >>= \case
        (Just t) -> seek t p k 
        Nothing  -> failFD4 $ "Variable global " ++ name ++ " no encontrada." 
    (V _ _)             -> failFD4 "seek no esperaba variables libres"
    (Const _ (CNat n))  -> destroy (Vall n) k
    (Lam _ n ty (Sc1 t)) -> destroy (ClosFun p n ty t) k
    (Fix _ n1 ty1 n2 ty2 (Sc2 t)) -> destroy (ClosFix p n1 ty1 n2 ty2 t) k
    (Let info n ty s (Sc1 t))   -> seek (App info (Lam info n ty (Sc1 t)) s) p k

destroy :: MonadFD4 m => Val          -> Kont -> m Val
destroy v ((PrintEval s):ks) = return v
destroy v ((OpLeftEval op p t):ks) = seek t p $ OpRightEval op v:ks
destroy (Vall n') ((OpRightEval op (Vall n)):ks) = destroy (Vall (semOp op n n')) ks
destroy (Vall 0) ((IfZEval p t1 _):ks) = seek t1 p ks
destroy (Vall n) ((IfZEval p _ t2):ks) = seek t2 p ks
destroy v ((AppEval p t):ks) = seek t p (Clos v:ks)
destroy v ((Clos val):ks) = case val of
    (ClosFun p _ _ t)     -> trace "PASÉ" $ seek t (v:p) ks
    (ClosFix p _ _ _ _ t) -> seek t (v:val:p) ks
    _                     -> failFD4 "Destroy esperaba clausura y recibio Vall"
destroy v [] = return v
destroy v ks = failFD4 $ "Destroy: valor no contemplado \n\t" ++ show v ++ "\n\t" ++ show (head ks)

-- ToDo: Agregar informa con de nombre
val2term :: Val -> TTerm
val2term (Vall n) = Const (NoPos, NatTy) (CNat n)
val2term (ClosFun vs n ty t) = let
    -- Todo: Refactorizar esto
    vs' = zip vs (reverse [1 .. (length vs)])
    c = foldl (\ term (caso, i) -> subst' i (val2term caso) (Sc1 term)) t vs'
    r = Lam (NoPos, FunTy ty (getTy t)) n ty $ Sc1 c
    in trace (show r) r
val2term (ClosFix vs n1 ty1 n2 ty2 t) = let
    vs' = zip vs (reverse [1 .. (length vs)])
    c = foldl (\ term (caso, i) -> trace ("\t-Reemplazando " ++ show caso ++ " en " ++ show term ++ "\n") subst' i (val2term caso) (Sc1 term)) t vs'
    in Fix (NoPos, ty1) n1 ty1 n2 ty2 $ Sc2 c

-- (fun (z:Nat) -> fun (x:Nat) -> fun (y:Nat) -> x+y+z) 1 2
-- (fun (w:Nat) -> fun (z:Nat) -> fun (x:Nat) -> fun (y:Nat) -> x+y+w+z) 8 9

-- Esta es una función auxiliar que usan el resto de las funciones de este módulo
-- para modificar las vsriables (ligadas y libres) de un término
varChanger' :: Int
           -> (Int -> info -> Name -> Tm info Var) --que hacemos con las variables localmente libres
           -> (Int -> info -> Int ->  Tm info Var) --que hacemos con los indices de De Bruijn
           -> Tm info Var -> Tm info Var
varChanger' n' local bound t' = go n' t' where
  go n   (V p (Bound i)) = bound n p i
  go n   (V p (Free x)) = local n p x
  go n   (V p (Global x)) = V p (Global x)
  go n (Lam p y ty (Sc1 t))   = Lam p y ty (Sc1 (go (n+1) t))
  go n (App p l r)   = App p (go n l) (go n r)
  go n (Fix p f fty x xty (Sc2 t)) = Fix p f fty x xty (Sc2 (go (n+2) t))
  go n (IfZ p c t e) = IfZ p (go n c) (go n t) (go n e)
  go n t@(Const _ _) = t
  go n (Print p str t) = Print p str (go n t)
  go n (BinaryOp p op t u) = BinaryOp p op (go n t) (go n u)
  go n (Let p v vty m (Sc1 o)) = Let p v vty (go n m) (Sc1 (go (n+1) o))

subst' :: Int -> Tm info Var -> Scope info Var -> Tm info Var
subst' k n (Sc1 m) = varChanger' k (\_ p n' -> V p (Free n')) bnd m
   where bnd depth p i
             | i == depth = n
             | otherwise  = V p (Bound i)