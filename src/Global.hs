{-|
Module      : Global
Description : Define el estado global del compilador
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}
module Global where

import Lang ( TTerm, Decl(Decl), Name, Ty )

data GlEnv = GlEnv {
  inter :: Bool,        --  ^ True, si estamos en modo interactivo.
                        -- Este parámetro puede cambiar durante la ejecución:
                        -- Es falso mientras se cargan archivos, pero luego puede ser verdadero.
  lfile :: String,      -- ^ Último archivo cargado.
  cantDecl :: Int,      -- ^ Cantidad de declaraciones desde la última carga
  glb :: [Decl TTerm],  -- ^ Entorno con declaraciones globales
  typeSynonym :: [(Name, Ty)], -- ^ Entorno de sinonimos de tipos
  statistics :: Statistics
}

data Statistics = StatsBytecode {
  opsBC :: Int,
  clausurasBC :: Int,
  maxPilaSize :: Int
  } 
  | StatsCEK {
    transitions :: Int,
    clausurasCEK :: Int
  }
  | Dummy
  deriving Show


-- ^ Entorno de tipado de declaraciones globales
tyEnv :: GlEnv ->  [(Name,Ty)]
tyEnv g = map (\(Decl _ n t b) -> (n, t))  (glb g)

{-
  Representa opciones para depurar la ejecución del bytecode en Haskell
-}
data DebugOptions = DebugOptions {
  enabledPrintBytecode :: Bool,
  enabledPrintStack    :: Bool,
  enablePrintEnv      :: Bool
}

defaultDebugOptions :: Maybe DebugOptions
defaultDebugOptions = Just $ DebugOptions False False False

fullDebugOptions :: Maybe DebugOptions
fullDebugOptions = Just $ DebugOptions True True True

data BytecodeType = BC8Bit | BC32Bit 
  deriving (Show, Eq)
  
{-
 Tipo para representar las banderas disponibles en línea de comando.
-}
data Mode =
    Interactive
  | Typecheck
  | Eval
  | EvalCEK
  | Bytecompile
  | Bytecompile8
  | RunVM
  | RunVM8
  | CC
  deriving Show
data Conf = Conf {
    prof :: Bool,
    opt :: Bool,          --  ^ True, si estan habilitadas las optimizaciones.
    modo :: Mode,
    byteCodeDebugOptions :: Maybe DebugOptions -- Solo se usa si el modo es Bytecompile
}

-- | Valor del estado inicial
initialEnv :: GlEnv
initialEnv = GlEnv False "" 0 [] [] Dummy
