{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

{-|
Module      : Main
Description : Compilador de FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline (getInputLine, runInputT, InputT, Settings (..) )
import Control.Monad.Catch (MonadMask)

--import Control.Monad
import Control.Monad.Trans
import Data.List (nub, isPrefixOf, intercalate )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( hPrint, stderr, hPutStrLn )
import Data.Maybe ( fromMaybe, isJust )

import System.Exit ( exitWith, ExitCode(ExitFailure) )
import Options.Applicative
import GHC.Base ( sequence )
import GHC.Base ( when ) -- Para que corra CI

import Global
import Errors
import Lang
import Parse ( P, tm, program, declOrTm, runP )
import Elab ( elab, elabDecl )
import Eval ( eval )
import PPrint ( pp , ppTy, ppDecl, openAll, colorear )
import MonadFD4
import TypeChecker ( tc, tcDecl )
import CEK
import Bytecompile8 (bytecompileModule, bcWrite, bcRead, runBC, showBC)
import Optimization (optDecls)
import C
import ClosureConvert
import System.Console.Haskeline.Completion (completeFilename)
import qualified Bytecompile32

defaultSettings :: MonadIO m => Settings m
defaultSettings = Settings
      { complete = completeFilename
      , historyFile = Just ".fd4_history"
      , autoAddHistory = True }

prompt :: String
prompt = "FD4> "



-- | Parser de banderas
parseMode :: Parser (Mode, Bool, Bool, Bool)
parseMode = (,,,) <$>
      (flag' Typecheck ( long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
      <|> flag' Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la BVM")
      <|> flag' RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la BVM")
      <|> flag' Bytecompile8 (long "bytecompile8" <> help "Compilar a la BVM de 8 bits")
      <|> flag' RunVM8 (long "runVM8" <> help "Ejecutar bytecode en la BVM de 8 bits")
      <|> flag Interactive Interactive ( long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
      <|> flag Eval        Eval        (long "eval" <> short 'e' <> help "Evaluar programa")
      <|> flag' CC ( long "cc" <> short 'c' <> help "Compilar a código C")
      )
   -- reemplazar por la siguiente línea para habilitar opción
      <*> flag False True (long "optimize" <> short 'o' <> help "Optimizar código")
      <*> flag False True (long "profile" <> short 'p' <> help "Activar profiling")
      <*> flag False True (long "cek" <> short 'k' <> help "Activar evaluación con máquina CEK")

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode, Bool, Bool, Bool, [FilePath])
parseArgs = (\(a, opt, prof, cek) c -> (a, opt, prof, cek, c)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= \x@(a,b,c,d,_) ->
  go x
  where
    opts = info (parseArgs <**> helper)
      ( fullDesc
     <> progDesc "Compilador de FD4"
     <> header "Compilador de FD4 de la materia Compiladores 2023" )

    --     Modo, optimizar, profiling, cek, archivos
    go :: (Mode,Bool,Bool,Bool,[FilePath]) -> IO ()
    go (Interactive, opt, prof, False,files) =
              runOrFail (Conf prof opt Interactive Nothing) (runInputT defaultSettings (repl files) >> mapM_ compileFile files)    -- go (Eval ,opt, prof, True,files) =    --           runOrFail (Conf prof opt EvalCEK) (runInputT defaultSettings (repl files) >>  mapM_ compileFile files)    -- go (Eval ,opt, prof, False, files) =    --           runOrFail (Conf prof opt Eval) (runInputT defaultSettings (repl files) >>  mapM_ compileFile files)
    -- ToDo: Agregar soporte para personalizar opciones depuración
    go (Bytecompile, opt, prof, cek, files) =
              runOrFail (Conf prof opt Bytecompile Nothing) $ mapM_ (byteCompileFile BC32Bit)  files
    go (RunVM, opt, prof, cek, files) =
              runOrFail (Conf prof opt RunVM (if prof then fullDebugOptions else defaultDebugOptions)) $ mapM_ (byteRunVmFile BC32Bit) files
    go (Bytecompile8, opt, prof, cek, files) =
              runOrFail (Conf prof opt Bytecompile8 Nothing) $ mapM_ (byteCompileFile BC8Bit)  files
    go (RunVM8, opt, prof, cek, files) =
              runOrFail (Conf prof opt RunVM8 (if prof then fullDebugOptions else defaultDebugOptions)) $ mapM_ (byteRunVmFile BC8Bit) files
    go (CC, opt, prof, cek, files) =
              runOrFail (Conf prof opt CC Nothing) $ mapM_ ccCopileFile files
    go (m, opt, prof, cek, files) =
              runOrFail (Conf prof opt (if cek then EvalCEK else m) Nothing) $ mapM_ compileFile files

runOrFail :: Conf -> FD4 a -> IO a
runOrFail c m = do
  r <- runFD4 m c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

repl :: (MonadFD4 m, MonadMask m) => [FilePath] -> InputT m ()
repl args = do
       lift $ setInter True
       lift $ catchErrors $ mapM_ compileFile args
       s <- lift get
       when (inter s) $ liftIO $ putStrLn
         (  "Entorno interactivo para FD4.\n"
         ++ "Escriba :? para recibir ayuda.")
       loop
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c
                       maybe loop (`when` loop) b

loadFile ::  MonadFD4 m => FilePath -> m [SDecl STerm]
loadFile f = do

    let filename = reverse (dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    setLastFile filename
    parseIO filename program x

compileFile ::  MonadFD4 m => FilePath -> m ()
compileFile f = do
    i <- getInter
    setInter False
    when i $ printFD4 ("Abriendo "++f++"...")
    decls <- loadFile f
    ds <- mapM processDecl decls
    opt <- getOpt
    let ds'' = map (\(Just d) -> d) $ filter isJust ds
    ds' <- if opt then optDecls ds'' else return ds''
    mapM_ handleDecl' ds'
    setInter i

processDecl :: MonadFD4 m => SDecl STerm -> m (Maybe (Decl TTerm))
processDecl x = do 
    x1 <- elabDecl x
    case x1 of
      Nothing -> return Nothing
      Just x2 -> do
        x3 <- typecheckDecl x2
        addDecl x3
        return $ Just x3

byteCompileFile ::  MonadFD4 m => BytecodeType -> FilePath -> m ()
byteCompileFile bt f = do
    printFD4 ("Abriendo " ++ f ++ "...")
    sdecls <- loadFile f
    mdecls <- mapM elabDecl sdecls
    -- let sdecl = GHC.Base.sequence mdecls
    let sdecl = filter isJust mdecls
    prog <- case sdecl of
      [] -> failFD4 "Error de compilacion o Compilacion vacia"
      decl ->  mapM (\(Just sd) -> typecheckDecl sd >>= \d -> addDecl d >> return d) decl
    printFD4 $  "Compilando " ++ f ++ " a bytecode "
    case bt of
      BC32Bit -> byteCompileFile32 prog f
      BC8Bit  -> byteCompileFile8 prog f

byteCompileFile32 :: MonadFD4 m => Module -> [Char] -> m ()
byteCompileFile32 prog f = do
  bytecode <- Bytecompile32.bytecompileModule prog
  prof <- getProf
  when prof (printFD4 $ Bytecompile32.showBC bytecode)
  let fp = changeExtension f "bc32"
  printFD4 $ "Escribiendo bytecode a " ++ fp
  liftIO (Bytecompile32.bcWrite bytecode fp)

byteCompileFile8 :: MonadFD4 m => Module -> [Char] -> m ()
byteCompileFile8 prog f = do
  bytecode <- Bytecompile8.bytecompileModule prog
  prof <- getProf
  when prof (printFD4 $ Bytecompile8.showBC bytecode)
  let fp = changeExtension f "bc8"
  printFD4 $ "Escribiendo bytecode a " ++ fp
  liftIO (Bytecompile8.bcWrite bytecode fp)

changeExtension :: FilePath -> String -> FilePath
changeExtension f e = (reverse . dropWhile (/= '.') . reverse) f ++ e

byteRunVmFile :: MonadFD4 m => BytecodeType -> FilePath -> m ()
byteRunVmFile bt f = do
  --printFD4 ("Abriendo " ++ f ++ "...")
  --bs <- liftIO $ bcRead f
  --printFD4 (showBC bs)
  --runBC bs
  case bt of
    BC32Bit -> (liftIO . Bytecompile32.bcRead) f >>= Bytecompile32.runBC
    BC8Bit  -> (liftIO . Bytecompile8.bcRead) f >>= Bytecompile8.runBC
  profEnabled <- getProf
  when profEnabled (do
    s <- gets statistics
    let (StatsBytecode op cl mp) = s
    printFD4 $ "Numero de ops: " ++ show op ++
              "\nNumero de clausuras: " ++ show cl ++
              "\nTamano maximo pila: " ++ show mp ++
              "\n")



ccCopileFile :: MonadFD4 m => FilePath -> m ()
ccCopileFile f = do
  printFD4 ("Abriendo " ++ f ++ "...")
  sdecls <- loadFile f
  mdecls <- mapM elabDecl sdecls
  let sdecl = (GHC.Base.sequence . filter isJust) mdecls
  --let sdecl = Just [ x | Just x <- mdecls ]
  prog <- case sdecl of
    Nothing -> failFD4 "Error de compilacion"
    Just decl ->  mapM (\sd -> typecheckDecl sd >>= \d -> addDecl d >> return d) decl
  printFD4 $  "Compilando " ++ f ++ " a C "
  let ir = runCC prog
  let sourceC = ir2C ir
  liftIO $ writeFile (changeExtension f "c") sourceC

parseIO ::  MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

evalDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
evalDecl (Decl p x t e) = do
    e' <- eval e
    return (Decl p x t e')

-- handleDecl ::  MonadFD4 m => SDecl STerm -> m ()
-- handleDecl d = elabDecl d >>= \case
--   (Just d') -> handleDecl' d'
--   Nothing   -> return ()

handleDecl' ::  MonadFD4 m => Decl TTerm -> m ()
handleDecl' td@(Decl p x t tt) = do
        m <- getMode
        case m of
          Interactive -> do
              te <- eval tt
              addDecl (Decl p x t te)
          Typecheck -> do
              f <- getLastFile
              printFD4 ("Chequeando tipos de "++f)
              addDecl td
              ppterm <- ppDecl td  --td'
              printFD4 ppterm
          Eval -> do
              ed <- evalDecl td
              addDecl ed
          EvalCEK -> do
            v <- seek tt
            let tt' = val2term v
            let decl' = Decl p x t tt'
            ppterm <- ppDecl decl'
            addDecl $ Decl p x t $ val2term v
            profEnabled <- getProf
            when profEnabled (do
              s <- gets statistics
              let (StatsCEK pasos c) = s
              printFD4 $ "Numero de pasos: " ++ show pasos ++
                        "\nNumero de clausuras: " ++ show c ++
                        "\n")
          _ -> undefined

typecheckDecl :: MonadFD4 m => Decl STerm -> m (Decl TTerm)
typecheckDecl (Decl p x ty t) = do
  term <- elab t
  decl@(Decl _ _ _ tt) <- tcDecl (Decl p x ty term)
  opt <- getOpt
  prof <- getProf
  when prof (printFD4 "Optimizando...")
  return decl

  -- if opt then
  --   when prof (printFD4 "Optimizando...") >>
  --   -- printFD4 "Optimizando..." >>
  --   optimizeTerm tt >>= \tt' ->
  --   return (Decl p x ty tt')
  -- else
  --   return decl


data Command = Compile CompileForm
             | PPrint String
             | Type String
             | Reload
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if ":" `isPrefixOf` x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   intercalate ", " ([ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   PPrint          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":reload"]      ""        (const Reload)         "Vuelve a cargar el último archivo cargado",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = intercalate ", " (map (++ if null a then "" else " " ++ a) c)
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadFD4 m => Command  -> m Bool
handleCommand cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printFD4 (helpTxt commands) >> return True
       Browse ->  do  printFD4 (unlines (reverse (nub (map declName glb))))
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e
                          CompileFile f        -> compileFile f
                      return True
       Reload ->  eraseLastFileDecls >> (getLastFile >>= compileFile) >> return True
       PPrint e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase ::  MonadFD4 m => String -> m ()
compilePhrase x = do
    dot <- parseIO "<interactive>" declOrTm x
    case dot of
      Left d  -> processDecl d >>= \case
        Nothing -> return ()
        Just d' -> handleDecl' d'
      Right t -> handleTerm t

-- handleTerm ::  MonadFD4 m => STerm -> m ()
-- handleTerm t = do
--         t' <- elab t
--         s <- get
--         tt <- tc t' (tyEnv s)
--         te <- eval tt
--         ppte <- pp te
--         printFD4 (ppte ++ " : " ++ ppTy (getTy tt))

handleTerm ::  MonadFD4 m => STerm -> m ()
handleTerm t = do
  m <- getMode
  t' <- elab t
  s <- get
  tt <- tc t' (tyEnv s)
  te <- eval tt
  ppte <- pp te
  printFD4 (ppte ++ " : " ++ ppTy (getTy tt))

printPhrase   :: MonadFD4 m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" tm x
    ex <- elab x'
    tyenv <- gets tyEnv
    tex <- tc ex tyenv
    t  <- case x' of
           (SV p f) -> fromMaybe tex <$> lookupDecl f
           _       -> return tex

    gdecl <- gets glb
    let dt = openAll fst (map declName gdecl) t
    printFD4 $ colorear "STerm"
    printFD4 (show dt)
    printFD4 $ colorear "TTerm"
    printFD4 (show t)

typeCheckPhrase :: MonadFD4 m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" tm x
         t' <- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         let ty = getTy tt
         printFD4 (ppTy ty)
