{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab ( elab, elabDecl) where

import Lang
import Subst
import MonadFD4 (lookupTyS, addTyS, MonadFD4, lookupTyS, failFD4)

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: STerm -> Term
elab = elab' []

elab' :: [Name] -> STerm -> Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env 
    then  V p (Free v)
    else V p (Global v)

elab' _ (SConst p c) = Const p c
-- elab' env (SLam p (v,ty) t) = Lam p v ty (close v (elab' (v:env) t))
-- elab' env (SFix p (f,fty) (x,xty) t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) t))
elab' env (SIfZ p c t e)         = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operadores binarios
elab' env (SBinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Operador Print
elab' env (SPrint i str t) = Print i str (elab' env t)
-- Aplicaciones generales
elab' env (SApp p h a) = App p (elab' env h) (elab' env a)
elab' env (SLet p recursive (v,vty) def body) =  
  Let p v vty (elab' env def) (close v (elab' (v:env) body))
elab' env (SLet p recursive bs def body) = undefined
  -- elabLet p recursive (head bs) (tail def) def body
  -- case (recursive, bs) of 
  --   (False, [(v, vty)]) -> Let p v vty (elab' env def) (close v (elab' (v:env) body))
  --   (False, [(v, vty):bs]) -> Let p v vty (elab' env def) (close v (elab' (v:env) body))

elabLet p env False (v, vty) [] def body = 
  Let p v vty (elab' env def) (close v (elab' (v:env) body))
elabLet p env False (v, vty) [(x,xty)] def body = 
  Let p v (FunTy xty vty) (Lam p (close x (elab' p (x:env) def))) (close v (elab' (v:env) body))
elabLet p env False (v, vty) ((x,xty):bs) def body = 
  Let p v () () (elabClose v env body)

elabSTy :: MonadFD4 m => SType -> m Ty
elabSTy SNatTy = return NatTy
elabSTy (SFunTy t1 t2) = do 
  ft1 <- elabSTy t1
  ft2 <- elabSTy t2
  return $ FunTy ft1 ft2
elabSTy (STyS v t) = do
  ty <- elabSTy t
  addTyS v ty
  return ty
elabSTy (SVT v) = do 
  ty <- lookupTyS v
  case ty of 
    Just t -> return t
    Nothing -> failFD4 $ "No se encontro el sinónimo de tipo " ++ v

elabDecl :: Decl STerm -> Decl Term
elabDecl = fmap elab

elabClose x env term = close x (elab' (x:env) term)