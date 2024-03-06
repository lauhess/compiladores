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
import Common (Pos)

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: MonadFD4 m => STerm -> m Term
elab = elab' []

elab' :: MonadFD4 m => [Name] -> STerm -> m Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  return $ if v `elem` env
         then V p (Free v)
         else V p (Global v)

elab' _ (SConst p c) = return $ Const p c
elab' env (SLam p [(v,vty)] t) = do
  vElabType <- elabSTy vty
  closedTerm <- elabClose v env t
  return $ Lam p v vElabType closedTerm
elab' env (SLam p ((v,vty):vs) t) = do
  vElabType <- elabSTy vty
  closedTerm <- elabClose v env (SLam p vs t)
  return $ Lam p v vElabType closedTerm
elab' env (SIfZ p c t e) = do
  cElab <- elab' env c
  tElab <- elab' env t
  eElab <- elab' env e
  return $ IfZ p cElab tElab eElab
-- Operadores binarios
elab' env (SBinaryOp i o t u) = do
  tElab <- elab' env t
  uElab <- elab' env u
  return $ BinaryOp i o tElab uElab
-- Operador Print
elab' env (SPrint i str t) = do
  tElab <- elab' env t
  return $ Print i str tElab
-- Aplicaciones generales
elab' env (SApp p h a) = do
  hElab <- elab' env h
  aElab <- elab' env a
  return $ App p hElab aElab
  --Let p v vty (elab' env def) (close v (elab' (v:env) body))
elab' env (SLet p recursive bs def body) = do
  -- elabType <- elabSTy $ snd (head bs)
  elabLet p env recursive (head bs) (tail bs) def body
elab' env (SFix info [(f, fty),(x, xty)] body) = do
  bElab <- elabClose2 f x env body
  ftyElab <- elabSTy fty
  xtyElab <- elabSTy xty
  return $ Fix info f ftyElab x xtyElab bElab
elab' env (SFix info (fun:x:xs) body) = do
  bElab <- elabClose2 (fst fun) (fst x) env (SLam info xs body)
  ftyElab <- elabSTy $ snd fun
  xtyElab <- elabSTy $ snd x
  return $ Fix info (fst fun) ftyElab (fst x) xtyElab bElab

elab' _ _ = undefined
  -- elabLet p recursive (head bs) (tail def) def body
  -- case (recursive, bs) of 
  --   (False, [(v, vty)]) -> Let p v vty (elab' env def) (close v (elab' (v:env) body))
  --   (False, [(v, vty):bs]) -> Let p v vty (elab' env def) (close v (elab' (v:env) body))

---------------------
{- Resolucion Let -}
---------------------
elabLet :: MonadFD4 m => Pos -> [Name] -> Bool -> (Name, SType) -> [(Name, SType)] -> STerm -> STerm -> m Term
elabLet p env  False (v, vty') [] def body = do          -- Definicion original (var valor)
  vty <- elabSTy vty'
  defElab <- elab' env def
  bodyElab <- elabClose v env body
  return $ Let p v vty defElab bodyElab
elabLet p env  False (v, vty) [(x,xty)] def body = do   -- Definicion funcion ariedad 1
  vType <- elabSTy vty
  defElab <- elab' env (SLam p [(x,xty)] def)
  xType <- elabSTy xty
  bodyElab <- elabClose v env body
  return $ Let p v (FunTy xType vType) defElab bodyElab
elabLet p env  False (v, vty') xs def body = do          -- Definicion funcion ariedad n
  vty <- elabSTy vty'
  fty <- makeType xs vty
  defElab <- elab' env (SLam p xs def)
  bodyElab <- elabClose v env body
  def' <- elab' env (SLam p xs def)
  return $ Let p v fty defElab bodyElab
---------------------
{- Resolucion Let Rec -}
---------------------

elabLet p env  True (f, fty') [(x,xty)] def body = do    -- Ariedad 1
  fty <- elabSTy fty'
  elabXty <- elabSTy xty
  body' <- elabClose f env body
  defClose2 <- elabClose2 f x env def
  let  def' = Fix p f (FunTy elabXty fty) x elabXty defClose2
  return $ Let p f (FunTy elabXty fty) def' body'
elabLet p env  True (f, fty) ((x,xty):xs) def body = do           -- Ariedad n
  let fty' = makeSType xs fty
  let fun = SLam p xs def
  elab' env $ SLet p True [(f,fty'), (x,xty)] fun body
  where
    makeSType :: [(Name, SType)] -> SType -> SType
    makeSType [] vty = vty
    makeSType ((_,t):ts) vty =
      let
        ts' = makeSType ts vty
      in SFunTy t ts'

elabLet _ _ _ _ _ _ _ = undefined


---------------------
{- Elaboracion de Tipos -}
---------------------

elabSTy :: MonadFD4 m => SType -> m Ty
elabSTy SNatTy = return NatTy
elabSTy (SFunTy t1 t2) = do
  ft1 <- elabSTy t1
  ft2 <- elabSTy t2
  return $ FunTy ft1 ft2
elabSTy (SVT v) = do
  ty <- lookupTyS v
  case ty of
    Just t -> return t
    Nothing -> failFD4 $ "No se encontro el sinónimo de tipo " ++ v

---------------------
{- Elaboracion de Declaraciones -}
---------------------
elabDecl :: MonadFD4 m => SDecl STerm -> m (Maybe (Decl STerm))
-- elabDecl = fmap elab
elabDecl (SDecl pos False [(x, xty)] def) =             -- Definicion original
  elabSTy xty >>= \t -> return $ Just $ Decl pos x t def
elabDecl (SDecl pos False ((x, xty):xs) def) = do       -- funcion ariedad multiple
  t' <- elabSTy xty
  t <- makeType xs t'
  return $ Just $ Decl pos x t $ SLam pos xs def
elabDecl (SDecl pos True [(x, xty), (y, yty)] def) = do -- Fix ariedad simple
  xty' <- elabSTy xty
  yty' <- elabSTy yty
  return $ Just $ Decl pos x (FunTy yty' xty') (SFix pos [(x, SFunTy yty xty), (y, yty)] def)
elabDecl (SDecl pos True (fun:x:xs) def) = do           -- Fix ariedad multiple
  let fty' = makeSType xs (snd fun)
  let def' = SLam pos xs def
  elabDecl $ SDecl pos True [(fst fun, fty'), x] def'
  where
    makeSType :: [(Name, SType)] -> SType -> SType
    makeSType [] vty = vty
    makeSType ((_,t):ts) vty =
      let
        ts' = makeSType ts vty
      in SFunTy t ts'
elabDecl (SDeclTy pos s sty) = do                       -- Nueva declaracion de sinonimo de tipo
  t <- elabSTy sty
  addTyS s t
  return Nothing
elabDecl _ = undefined

elabClose :: MonadFD4 m => Name -> [Name] -> STerm -> m (Scope Pos Var)
elabClose x env term = do
  t <- elab' (x:env) term
  return $ close x t

elabClose2 :: MonadFD4 m => Name -> Name -> [Name] -> STerm -> m (Scope2 Pos Var)
elabClose2 x y env term = do
  t <- elab' (x:y:env) term
  return $ close2 x y t

makeType ::  MonadFD4 m => [(Name, SType)] -> Ty -> m Ty
makeType [] vty = return vty
makeType ((_,t):ts) vty = do
  ts' <- makeType ts vty
  t'  <- elabSTy t
  return $ FunTy  t' ts'