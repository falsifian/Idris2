module Idris.REPL.Common

import Core.Context.Log
import Core.Directory
import Core.Env
import Core.InitPrimitives
import Core.Metadata
import Core.Primitives
import Core.TT
import Core.Unify
import Core.UnifyState

import Idris.Doc.String
import Idris.Error
import Idris.IDEMode.Commands
import Idris.IDEMode.Holes
import Idris.Pretty
import public Idris.REPL.Opts
import Idris.Resugar
import Idris.Syntax
import Idris.Version

import Libraries.Data.ANameMap
import Libraries.Text.PrettyPrint.Prettyprinter

import Data.List
import System.File

%default covering

-- Output informational messages, unless quiet flag is set
export
iputStrLn : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            Doc IdrisAnn -> Core ()
iputStrLn msg
    = do opts <- get ROpts
         case idemode opts of
              REPL False => coreLift $ putStrLn !(render msg)
              REPL _ => pure ()
              IDEMode i _ f =>
                send f (SExpList [SymbolAtom "write-string",
                                 toSExp !(renderWithoutColor msg), toSExp i])


printWithStatus : {auto o : Ref ROpts REPLOpts} ->
                  Doc IdrisAnn -> Doc IdrisAnn -> Core ()
printWithStatus status msg
    = do opts <- get ROpts
         case idemode opts of
              REPL _ => coreLift $ putStrLn !(render msg)
              _      => pure () -- this function should never be called in IDE Mode

export
printResult : {auto o : Ref ROpts REPLOpts} ->
              Doc IdrisAnn -> Core ()
printResult msg = printWithStatus (pretty "ok") msg

-- Return that a protocol request failed somehow
export
printError : {auto o : Ref ROpts REPLOpts} ->
             Doc IdrisAnn -> Core ()
printError msg = printWithStatus (pretty "error") msg

DocCreator : Type -> Type
DocCreator a = a -> Core (Doc IdrisAnn)

export
emitProblem : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            {auto s : Ref Syn SyntaxInfo} ->
            a -> (DocCreator a) -> (DocCreator a) -> (a -> Maybe FC) -> Core ()
emitProblem a replDocCreator idemodeDocCreator getFC
    = do opts <- get ROpts
         case idemode opts of
              REPL _ =>
                  do msg <- replDocCreator a >>= render
                     coreLift $ putStrLn msg
              IDEMode i _ f =>
                  do msg <- idemodeDocCreator a
                     -- TODO: Display a better message when the error doesn't contain a location
                     case map toNonEmptyFC (getFC a) of
                          Nothing => iputStrLn msg
                          Just (origin, startPos, endPos) => do
                            fname <- case origin of
                              PhysicalIdrSrc ident => do
                                -- recover the file name relative to the working directory.
                                -- (This is what idris2-mode expects)
                                let fc = MkFC (PhysicalIdrSrc ident) startPos endPos
                                catch (nsToSource fc ident) (const $ pure "(File-Not-Found)")
                              PhysicalPkgSrc fname =>
                                pure fname
                              Virtual Interactive =>
                                pure "(Interactive)"
                            send f (SExpList [SymbolAtom "warning",
                                   SExpList [toSExp {a = String} fname,
                                            toSExp (addOne startPos),
                                              toSExp (addOne endPos),
                                              toSExp !(renderWithoutColor msg),
                                              -- highlighting; currently blank
                                              SExpList []],
                                    toSExp i])
  where
    addOne : (Int, Int) -> (Int, Int)
    addOne (l, c) = (l + 1, c + 1)

-- Display an error message from checking a source file
export
emitError : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            {auto s : Ref Syn SyntaxInfo} ->
            Error -> Core ()
emitError e = emitProblem e display perror getErrorLoc

export
emitWarning : {auto c : Ref Ctxt Defs} ->
              {auto o : Ref ROpts REPLOpts} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Warning -> Core ()
emitWarning w = emitProblem w displayWarning pwarning getWarningLoc

export
emitWarnings : {auto c : Ref Ctxt Defs} ->
               {auto o : Ref ROpts REPLOpts} ->
               {auto s : Ref Syn SyntaxInfo} ->
               Core (List Error)
emitWarnings
    = do defs <- get Ctxt
         let ws = reverse (warnings defs)
         session <- getSession
         if (session.warningsAsErrors)
           then let errs = WarningAsError <$> ws in
                errs <$ traverse_ emitError errs
           else [] <$ traverse_ emitWarning ws

export
emitWarningsAndErrors : {auto c : Ref Ctxt Defs} ->
                        {auto o : Ref ROpts REPLOpts} ->
                        {auto s : Ref Syn SyntaxInfo} ->
                        List Error -> Core (List Error)
emitWarningsAndErrors errs = do
  ws <- emitWarnings
  traverse_ emitError errs
  pure ws

getFCLine : FC -> Maybe Int
getFCLine = map startLine . isNonEmptyFC

export
updateErrorLine : {auto o : Ref ROpts REPLOpts} ->
                  List Error -> Core ()
updateErrorLine []
    = do opts <- get ROpts
         put ROpts (record { errorLine = Nothing } opts)
updateErrorLine (e :: _)
    = do opts <- get ROpts
         put ROpts (record { errorLine = (getErrorLoc e) >>= getFCLine } opts)

export
resetContext : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref MD Metadata} ->
               (origin : OriginDesc) ->
               Core ()
resetContext origin
    = do defs <- get Ctxt
         put Ctxt (record { options = clearNames (options defs) } !initDefs)
         addPrimitives
         put UST initUState
         put Syn initSyntax
         put MD (initMetadata origin)

public export
data EditResult : Type where
  DisplayEdit : Doc IdrisAnn -> EditResult
  EditError : Doc IdrisAnn -> EditResult
  MadeLemma : Maybe String -> Name -> IPTerm -> String -> EditResult
  MadeWith : Maybe String -> List String -> EditResult
  MadeCase : Maybe String -> List String -> EditResult

public export
data MissedResult : Type where
  CasesMissing : Name -> List String  -> MissedResult
  CallsNonCovering : Name -> List Name -> MissedResult
  AllCasesCovered : Name -> MissedResult

public export
data REPLResult : Type where
  Done : REPLResult
  REPLError : Doc IdrisAnn -> REPLResult
  Executed : PTerm -> REPLResult
  RequestedHelp : REPLResult
  Evaluated : IPTerm -> Maybe IPTerm -> REPLResult
  Printed : Doc IdrisAnn -> REPLResult
  TermChecked : IPTerm -> IPTerm -> REPLResult
  FileLoaded : String -> REPLResult
  ModuleLoaded : String -> REPLResult
  ErrorLoadingModule : String -> Error -> REPLResult
  ErrorLoadingFile : String -> FileError -> REPLResult
  ErrorsBuildingFile : String -> List Error -> REPLResult
  NoFileLoaded : REPLResult
  CurrentDirectory : String -> REPLResult
  CompilationFailed: REPLResult
  Compiled : String -> REPLResult
  ProofFound : IPTerm -> REPLResult
  Missed : List MissedResult -> REPLResult
  CheckedTotal : List (Name, Totality) -> REPLResult
  FoundHoles : List HoleData -> REPLResult
  OptionsSet : List REPLOpt -> REPLResult
  LogLevelSet : Maybe LogLevel -> REPLResult
  ConsoleWidthSet : Maybe Nat -> REPLResult
  ColorSet : Bool -> REPLResult
  VersionIs : Version -> REPLResult
  DefDeclared : REPLResult
  Exited : REPLResult
  Edited : EditResult -> REPLResult

export
docsOrSignature : {auto o : Ref ROpts REPLOpts} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  FC -> Name -> Core (List String)
docsOrSignature fc n
    = do syn  <- get Syn
         defs <- get Ctxt
         all@(_ :: _) <- lookupCtxtName n (gamma defs)
             | _ => undefinedName fc n
         let ns@(_ :: _) = concatMap (\n => lookupName n (defDocstrings syn))
                                     (map fst all)
             | [] => typeSummary defs
         pure [!(render styleAnn !(getDocsForName fc n MkConfig))]
  where
    typeSummary : Defs -> Core (List String)
    typeSummary defs = do Just def <- lookupCtxtExact n (gamma defs)
                            | Nothing => pure []
                          ty <- normaliseHoles defs [] (type def)
                          pure [(show n) ++ " : " ++ (show !(resugar [] ty))]

export
equivTypes : {auto c : Ref Ctxt Defs} ->
             (ty1 : ClosedTerm) ->
             (ty2 : ClosedTerm) ->
             Core Bool
equivTypes ty1 ty2 =
  do let False = isErased ty1
          | _ => pure False
     logTerm "typesearch.equiv" 10 "Candidate: " ty1
     defs <- get Ctxt
     True <- pure (!(getArity defs [] ty1) == !(getArity defs [] ty2))
       | False => pure False
     _ <- newRef UST initUState
     b <- catch
           (do res <- unify inTerm EmptyFC [] ty1 ty2
               case res of
                 (MkUnifyResult [] _ [] NoLazy) => pure True
                 _ => pure False)
           (\err => pure False)
     when b $ logTerm "typesearch.equiv" 20 "Accepted: " ty1
     pure b
