module Core.Value

import Core.Context
import Core.Core
import Core.Env
import Core.TT

import Libraries.Data.IntMap
import Libraries.Data.NameMap

%default covering

public export
data EvalOrder = CBV | CBN

public export
record EvalOpts where
  constructor MkEvalOpts
  holesOnly : Bool -- only evaluate hole solutions
  argHolesOnly : Bool -- only evaluate holes which are relevant arguments
  removeAs : Bool -- reduce 'as' patterns (don't do this on LHS)
  evalAll : Bool -- evaluate everything, including private names
  tcInline : Bool -- inline for totality checking
  fuel : Maybe Nat -- Limit for recursion depth
  reduceLimit : List (Name, Nat) -- reduction limits for given names. If not
                     -- present, no limit
  strategy : EvalOrder

export
defaultOpts : EvalOpts
defaultOpts = MkEvalOpts False False True False False Nothing [] CBN

export
withHoles : EvalOpts
withHoles = MkEvalOpts True True False False False Nothing [] CBN

export
withAll : EvalOpts
withAll = MkEvalOpts False False True True False Nothing [] CBN

export
withArgHoles : EvalOpts
withArgHoles = MkEvalOpts False True False False False Nothing [] CBN

export
tcOnly : EvalOpts
tcOnly = record { tcInline = True } withArgHoles

export
onLHS : EvalOpts
onLHS = record { removeAs = False } defaultOpts

export
cbn : EvalOpts
cbn = defaultOpts

export
cbv : EvalOpts
cbv = record { strategy = CBV } defaultOpts

mutual
  public export
  data LocalEnv : List Name -> List Name -> Type where
       Nil  : LocalEnv free []
       (::) : Closure free -> LocalEnv free vars -> LocalEnv free (x :: vars)

  public export
  data Closure : List Name -> Type where
       MkClosure : {vars : _} ->
                   (opts : EvalOpts) ->
                   LocalEnv free vars ->
                   Env Term free ->
                   Term (vars ++ free) -> Closure free
       MkNFClosure : EvalOpts -> Env Term free -> NF free -> Closure free

  -- The head of a value: things you can apply arguments to
  public export
  data NHead : List Name -> Type where
       NLocal : Maybe Bool -> (idx : Nat) -> (0 p : IsVar nm idx vars) ->
                NHead vars
       NRef   : NameType -> Name -> NHead vars
       NMeta  : Name -> Int -> List (Closure vars) -> NHead vars

  -- Values themselves. 'Closure' is an unevaluated thunk, which means
  -- we can wait until necessary to reduce constructor arguments
  public export
  data NF : List Name -> Type where
       NBind    : FC -> (x : Name) -> Binder (Closure vars) ->
                  (Defs -> Closure vars -> Core (NF vars)) -> NF vars
       -- Each closure is associated with the file context of the App node that
       -- had it as an argument. It's necessary so as to not lose file context
       -- information when creating the normal form.
       NApp     : FC -> NHead vars -> List (FC, Closure vars) -> NF vars
       NDCon    : FC -> Name -> (tag : Int) -> (arity : Nat) ->
                  List (FC, Closure vars) -> NF vars
       NTCon    : FC -> Name -> (tag : Int) -> (arity : Nat) ->
                  List (FC, Closure vars) -> NF vars
       NAs      : FC -> UseSide -> NF vars -> NF vars -> NF vars
       NDelayed : FC -> LazyReason -> NF vars -> NF vars
       NDelay   : FC -> LazyReason -> Closure vars -> Closure vars -> NF vars
       NForce   : FC -> LazyReason -> NF vars -> List (FC, Closure vars) -> NF vars
       NPrimVal : FC -> Constant -> NF vars
       NErased  : FC -> (imp : Bool) -> NF vars
       NType    : FC -> NF vars

export
ntCon : FC -> Name -> Int -> Nat -> List (FC, Closure vars) -> NF vars
ntCon fc (UN "Type") tag Z [] = NType fc
ntCon fc n tag Z [] = case isConstantType n of
  Just c => NPrimVal fc c
  Nothing => NTCon fc n tag Z []
ntCon fc n tag arity args = NTCon fc n tag arity args

export
getLoc : NF vars -> FC
getLoc (NBind fc _ _ _) = fc
getLoc (NApp fc _ _) = fc
getLoc (NDCon fc _ _ _ _) = fc
getLoc (NTCon fc _ _ _ _) = fc
getLoc (NAs fc _ _ _) = fc
getLoc (NDelayed fc _ _) = fc
getLoc (NDelay fc _ _ _) = fc
getLoc (NForce fc _ _ _) = fc
getLoc (NPrimVal fc _) = fc
getLoc (NErased fc i) = fc
getLoc (NType fc) = fc

export
{free : _} -> Show (NHead free) where
  show (NLocal _ idx p) = show (nameAt p) ++ "[" ++ show idx ++ "]"
  show (NRef _ n) = show n
  show (NMeta n _ args) = "?" ++ show n ++ "_[" ++ show (length args) ++ " closures]"

Show (Closure free) where
  show _ = "[closure]"

export
{free : _} -> Show (NF free) where
  show (NBind _ x (Lam _ c info ty) _)
    = "\\" ++ withPiInfo info (showCount c ++ show x ++ " : " ++ show ty) ++
      " => [closure]"
  show (NBind _ x (Let _ c val ty) _)
    = "let " ++ showCount c ++ show x ++ " : " ++ show ty ++
      " = " ++ show val ++ " in [closure]"
  show (NBind _ x (Pi _ c info ty) _)
    = withPiInfo info (showCount c ++ show x ++ " : " ++ show ty) ++
      " -> [closure]"
  show (NBind _ x (PVar _ c info ty) _)
    = withPiInfo info ("pat " ++ showCount c ++ show x ++ " : " ++ show ty) ++
      " => [closure]"
  show (NBind _ x (PLet _ c val ty) _)
    = "plet " ++ showCount c ++ show x ++ " : " ++ show ty ++
      " = " ++ show val ++ " in [closure]"
  show (NBind _ x (PVTy _ c ty) _)
    = "pty " ++ showCount c ++ show x ++ " : " ++ show ty ++
      " => [closure]"
  show (NApp _ hd args) = show hd ++ " [" ++ show (length args) ++ " closures]"
  show (NDCon _ n _ _ args) = show n ++ " [" ++ show (length args) ++ " closures]"
  show (NTCon _ n _ _ args) = show n ++ " [" ++ show (length args) ++ " closures]"
  show (NAs _ _ n tm) = show n ++ "@" ++ show tm
  show (NDelayed _ _ tm) = "%Delayed " ++ show tm
  show (NDelay _ _ _ _) = "%Delay [closure]"
  show (NForce _ _ tm args) = "%Force " ++ show tm ++ " [" ++ show (length args) ++ " closures]"
  show (NPrimVal _ c) = show c
  show (NErased _ _) = "[__]"
  show (NType _) = "Type"
