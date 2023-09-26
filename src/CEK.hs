module CEK where
import Lang
import MonadFD4
import Eval (semOp)

data Frame = 
    AppEval CEKEnv TTerm
    | Clos Val
    | IfZEval CEKEnv TTerm TTerm
    | OpLeftEval BinaryOp CEKEnv TTerm
    | OpRightEval BinaryOp Val 
    | PrintEval String
    deriving Show
    -- | LetEval CEKEnv TTerm

type Kont = [Frame]

data Val = 
      Vall Int 
    | ClosFun [Val] TTerm
    | ClosFix [Val] TTerm
    deriving Show
    -- | ClosLet [Val] Var TTerm TTerm

type CEKEnv = [Val]

seek    :: MonadFD4 m => TTerm -> CEKEnv -> Kont -> m Val
seek term p k = case term of 
    (Print _ s tm)      -> seek tm p $ PrintEval s : k
    (BinaryOp _ op t u) -> seek t p $ OpLeftEval op p u : k
    (IfZ _ c t u)       -> seek c p $ IfZEval p t u : k
    (App _ t u)         -> seek t p $ AppEval p u : k
    (V _ (Bound n))     -> destroy (p !! n) k 
    (V i (Global name)) -> lookupDecl name >>= (\(Just t) ->seek t p k) 
    (V _ _)             -> failFD4 "seek no esperaba variables libres"
    (Const _ (CNat n))  -> destroy (Vall n) k 
    (Lam _ _ _ (Sc1 t)) -> destroy (ClosFun p t) k
    (Fix _ _ _ _ _ (Sc2 t)) -> destroy (ClosFix p t) k
    -- (Let _ _ _ s (Sc1 t))   -> seek t p $ LetEval p s : k
    (Let info _ _ s (Sc1 t))   -> seek (App info t s) p k
    

destroy :: MonadFD4 m => Val          -> Kont -> m Val
destroy v ((PrintEval s):ks) = return v
destroy v ((OpLeftEval op p t):ks) = seek t p $ OpRightEval op v:ks
destroy (Vall n') ((OpRightEval op (Vall n)):ks) = return $ Vall $ semOp op n n' 
destroy (Vall 0) ((IfZEval p t1 _):ks) = seek t1 p ks
destroy (Vall n) ((IfZEval p _ t2):ks) = seek t2 p ks
destroy v ((AppEval p t):ks) = seek t p (Clos v:ks)
destroy v ((Clos val):ks) = case val of 
    (ClosFun p t) -> seek t (v:p) ks 
    (ClosFix p t) -> seek t (val:v:p) ks
    _             -> failFD4 "Destroy esperaba clausura y recibio Vall"
destroy v ks = failFD4 $ "Destroy: valor no contemplado \n\t" ++ show v ++ "\n\t" ++ show ks
    
val2term :: Val -> TTerm 
val2term _ = undefined 