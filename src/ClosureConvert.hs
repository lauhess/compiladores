module ClosureConvert where

import Lang

term2ir :: TTerm -> Ir
term2ir = undefined

ty2irTy :: Ty -> IrTy
ty2irTy = undefined 

decl2irDecl :: Decl TTerm -> IrDecl
decl2irDecl (Decl _ name NatTy t) = IrVal name IrInt (term2ir t)
decl2irDecl (Decl _ name (FunTy declTy retTy) t) = IrFun name (head $ ty2irTy retTy) (ty2irTy declTy) (term2ir t)

