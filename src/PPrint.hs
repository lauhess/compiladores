{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
{-|
Module      : PPrint
Description : Pretty printer para FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module PPrint (
    pp,
    ppTy,
    ppName,
    ppDecl,
    freshen,
    openAll,
    colorear
    ) where

import Lang
import Subst ( open, open2, unElabTy )
import Common ( Pos )

import Data.Text ( unpack )
import Prettyprinter.Render.Terminal
  ( renderStrict, italicized, color, colorDull, Color (..), AnsiStyle )
import Prettyprinter
    ( (<+>),
      annotate,
      defaultLayoutOptions,
      layoutSmart,
      nest,
      sep,
      parens,
      Doc,
      Pretty(pretty) )
import MonadFD4 ( gets, MonadFD4 )
import Global ( GlEnv(glb) )

colorear :: String -> String
colorear = render . opColor . pretty

freshen :: [Name] -> Name -> Name
freshen ns n = let cands = n : map (\i -> n ++ show i) [0..]
               in head (filter (`notElem` ns) cands)

-- | 'openAll' convierte términos locally nameless
-- a términos fully named abriendo todos las variables de ligadura que va encontrando
-- Debe tener cuidado de no abrir términos con nombres que ya fueron abiertos.
-- Estos nombres se encuentran en la lista ns (primer argumento).
openAll :: (i -> Pos) -> [Name] -> Tm i Var -> STerm
openAll gp ns (V p v) = case v of
      Bound i ->  SV (gp p) $ "(Bound "++show i++")" --este caso no debería aparecer
                                               --si el término es localmente cerrado
      Free x -> SV (gp p) x
      Global x -> SV (gp p) x
openAll gp ns (Const p c) = SConst (gp p) c
openAll gp ns (Lam p x ty t) =
  let x' = freshen ns x
      ty' = unElabTy ty
      t' = openAll gp (x':ns) (open x' t)
      (xs, res) = case t' of
        (SLam p' xs' res') -> if p' == gp p
                            then (xs', res')
                            else ([], t')
        _ -> ([], t')
  in SLam (gp p) ((x', ty'):xs) res
openAll gp ns (App p t u) = SApp (gp p) (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Fix p f fty x xty t) =
  let
    x' = freshen ns x
    f' = freshen (x':ns) f
    sfty = unElabTy fty
    sxty = unElabTy xty
    t' = openAll gp (x':f':ns) (open2 f' x' t)
    (xs, res) = case t' of
        (SLam p' xs' res') -> if p' == gp p
                            then (xs', res')
                            else ([], t')
        _ -> ([], t')
  in SFix (gp p) ((f', sfty):(x', sxty):xs) res
openAll gp ns (IfZ p c t e) = SIfZ (gp p) (openAll gp ns c) (openAll gp ns t) (openAll gp ns e)
openAll gp ns (Print p str t) = SPrint (gp p) str (openAll gp ns t)
openAll gp ns (BinaryOp p op t u) = SBinaryOp (gp p) op (openAll gp ns t) (openAll gp ns u)
--decorar     (Let (p,_) v vty def body) = do
openAll gp ns (Let p v ty m n) =
    let v'= freshen ns v
        def = openAll gp ns m
        body = openAll gp (v':ns) (open v' n)
        (xs, res, bool) = case def of
          SLam p' xs' res' | p' == gp p -> (xs', res', False)
          SFix p' (_:xs') res' | p' == gp p -> (xs', res', True)
          _ -> ([], def, False)
    in  SLet (gp p) bool [(v', unElabTy ty)] res body

--Colores
constColor :: Doc AnsiStyle -> Doc AnsiStyle
constColor = annotate (color Red)
opColor :: Doc AnsiStyle -> Doc AnsiStyle
opColor = annotate (colorDull Green)
keywordColor :: Doc AnsiStyle -> Doc AnsiStyle
keywordColor = annotate (colorDull Green) -- <> bold)
typeColor :: Doc AnsiStyle -> Doc AnsiStyle
typeColor = annotate (color Blue <> italicized)
typeOpColor :: Doc AnsiStyle -> Doc AnsiStyle
typeOpColor = annotate (colorDull Blue)
defColor :: Doc AnsiStyle -> Doc AnsiStyle
defColor = annotate (colorDull Magenta <> italicized)
nameColor :: Doc AnsiStyle -> Doc AnsiStyle
nameColor = id

-- | Pretty printer de nombres (Doc)
name2doc :: Name -> Doc AnsiStyle
name2doc n = nameColor (pretty n)

-- |  Pretty printer de nombres (String)
ppName :: Name -> String
ppName = id

ty2doc :: Ty -> Doc AnsiStyle
ty2doc (NatTy "")     = typeColor (pretty "Nat")
ty2doc (NatTy  s)     = typeColor (pretty s)
ty2doc (FunTy "" x@(FunTy _ _ _) y) = sep [parens (ty2doc x), typeOpColor (pretty "->"),ty2doc y]
ty2doc (FunTy souter x@(FunTy _ _ _) y) = sep [parens (typeColor (pretty souter)), typeOpColor (pretty "->"),ty2doc y]
ty2doc (FunTy "" x y) = sep [ty2doc x, typeOpColor (pretty "->"),ty2doc y]
ty2doc (FunTy s x y) = sep [typeColor (pretty s)]

-- | Pretty printer para tipos (Doc)
sty2doc :: SType -> Doc AnsiStyle
sty2doc SNatTy     = typeColor (pretty "Nat")
sty2doc (SFunTy x@(SFunTy _ _) y) = sep [parens (sty2doc x), typeOpColor (pretty "->"), sty2doc y]
sty2doc (SFunTy x y) = sep [sty2doc x, typeOpColor (pretty "->"), sty2doc y]
sty2doc (SVT v) = typeColor $ pretty v

-- | Pretty printer para tipos (String)
ppTy :: Ty -> String
ppTy = render . ty2doc

ppSTy :: SType -> String
ppSTy = render . sty2doc

c2doc :: Const -> Doc AnsiStyle
c2doc (CNat n) = constColor (pretty (show n))

binary2doc :: BinaryOp -> Doc AnsiStyle
binary2doc Add = opColor (pretty "+")
binary2doc Sub = opColor (pretty "-")

collectApp :: STerm -> (STerm, [STerm])
collectApp = go [] where
  go ts (SApp _ h tt) = go (tt:ts) h
  go ts h = (h, ts)

parenIf :: Bool -> Doc a -> Doc a
parenIf True = parens
parenIf _ = id

showIfTrue :: Bool -> String -> Doc a
showIfTrue True str = pretty str
showIfTrue _ _ = pretty ""

-- t2doc at t :: Doc
-- at: debe ser un átomo
-- | Pretty printing de términos (Doc)
t2doc :: Bool     -- Debe ser un átomo? 
      -> STerm    -- término a mostrar
      -> Doc AnsiStyle
-- Uncomment to use the Show instance for STerm
{- t2doc at x = text (show x) -}
t2doc at (SV _ x) = name2doc x
t2doc at (SConst _ c) = c2doc c
t2doc at (SLam p [x] (SPrint p' str _)) | p == p' =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str)]
t2doc at (SLam _ xs t) =
  parenIf at $
  sep [sep ([ keywordColor (pretty "fun") ] ++
           map binding2doc xs  ++
           [opColor (pretty "->")])
      , nest 2 (t2doc False t)]

t2doc at t@(SApp _ _ _) =
  let (h, ts) = collectApp t in
  parenIf at $
  t2doc True h <+> sep (map (t2doc True) ts)

t2doc at (SFix _ ((x,xty):ys) m) =
  parenIf at $
  sep [ sep ([keywordColor (pretty "fix")
                  , binding2doc (x,xty)] ++
                   map binding2doc ys ++
                  [opColor (pretty "->") ])
      , nest 2 (t2doc False m)
      ]
t2doc at (SIfZ _ c t e) =
  parenIf at $
  sep [keywordColor (pretty "ifz"), nest 2 (t2doc False c)
     , keywordColor (pretty "then"), nest 2 (t2doc False t)
     , keywordColor (pretty "else"), nest 2 (t2doc False e) ]

t2doc at (SPrint _ str t) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str), t2doc True t]

t2doc at (SLet _ bool ((v,ty):ys) t t') =
  parenIf at $
  sep [
    sep ([keywordColor (pretty "let")
         , showIfTrue bool "rec"
         , binding2doc (v,ty)] ++
         map binding2doc ys ++
        [opColor (pretty "=")])
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (SBinaryOp _ o a b) =
  parenIf at $
  t2doc True a <+> binary2doc o <+> t2doc True b

t2doc _ _ = undefined

binding2doc :: (Name, SType) -> Doc AnsiStyle
binding2doc (x, ty) =
  parens (sep [name2doc x, pretty ":", sty2doc ty])

-- | Pretty printing de términos (String)
pp :: MonadFD4 m => TTerm -> m String
-- Uncomment to use the Show instance for Term
{- pp = show -}
pp t = do
       gdecl <- gets glb
       return (render . t2doc False $ openAll fst (map declName gdecl) t)

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

-- | Pretty printing de declaraciones
ppDecl :: MonadFD4 m => Decl TTerm -> m String
ppDecl (Decl p x xty t) = do
  gdecl <- gets glb
  let sterm = (openAll fst (map declName gdecl) t) 
      (variables, cuerpo) = sacarVars x p sterm
      variablesDecoradas = map binding2doc variables
      esrec = esRec sterm
      hola = defColor (pretty "let"): esrec ++ name2doc x : variablesDecoradas ++ [defColor (pretty "=")]
  return (render $ sep hola
                   <+> nest 2 (t2doc False cuerpo))

esRec :: STerm -> [Doc AnsiStyle]
esRec (SFix _ _ _) = [defColor (pretty "rec")]
esRec _ = []

sacarVars :: Name -> Pos -> STerm -> ([(Name, SType)], STerm)
sacarVars _ posDecl l@(SLam posLam vars cuerpo) = 
    if posLam == posDecl
    then (vars,cuerpo)
    else ([], l)
sacarVars nameDecl posDecl l@(SFix posLam vars cuerpo) = 
    if posLam == posDecl
    then let
      (name, _) = head vars
      cuerpo' = cambiarNobre nameDecl name cuerpo
      in (tail vars,cuerpo')
    else ([], l)
sacarVars _ _ p = ([], p) 

cambiarNobre:: Name -> Name -> STerm -> STerm
cambiarNobre destino origen (SV p x) = SV p (if x == origen then destino else x)
cambiarNobre destino origen c@(SConst _ _) = c
cambiarNobre destino origen (SLam p vars cuerpo) = 
    SLam p (map (\(x,ty) -> (if x == origen then destino else x, ty)) vars) (cambiarNobre destino origen cuerpo)
cambiarNobre destino origen (SApp p t u) = SApp p (cambiarNobre destino origen t) (cambiarNobre destino origen u)
cambiarNobre destino origen (SPrint p str t) = SPrint p str (cambiarNobre destino origen t)
cambiarNobre destino origen (SIfZ p c t e) = SIfZ p (cambiarNobre destino origen c) (cambiarNobre destino origen t) (cambiarNobre destino origen e)
cambiarNobre destino origen (SBinaryOp p op t u) = SBinaryOp p op (cambiarNobre destino origen t) (cambiarNobre destino origen u)
cambiarNobre destino origen (SFix p vars cuerpo) = 
    SFix p (map (\(x,ty) -> (if x == origen then destino else x, ty)) vars) (cambiarNobre destino origen cuerpo)
cambiarNobre destino origen (SLet p bool vars t t') =
    SLet p bool (map (\(x,ty) -> (if x == origen then destino else x, ty)) vars) (cambiarNobre destino origen t) (cambiarNobre destino origen t')
