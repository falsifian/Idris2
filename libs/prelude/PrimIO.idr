module PrimIO

import Builtin

%default total

public export
data IORes : Type -> Type where
     MkIORes : (result : a) -> (1 x : %World) -> IORes a

||| Idris's primitive IO, for building abstractions on top of.
public export
PrimIO : Type -> Type
PrimIO a = (1 x : %World) -> IORes a

export
prim__io_pure : a -> PrimIO a
prim__io_pure = MkIORes

export
prim__io_bind : (1 act : PrimIO a) -> (1 k : a -> PrimIO b) -> PrimIO b
prim__io_bind fn k w
    = let MkIORes x' w' = fn w in k x' w'

-- A pointer representing a given parameter type
-- The parameter is a phantom type, to help differentiate between
-- different pointer types
public export
data Ptr : Type -> Type where [external]

-- A pointer to any type (representing a void* in foreign calls)
public export
data AnyPtr : Type where [external]

-- As Ptr, but associated with a finaliser that is run on garbage collection
public export
data GCPtr : Type -> Type where [external]

-- As AnyPtr, but associated with a finaliser that is run on garbage collection
public export
data GCAnyPtr : Type where [external]

public export
data ThreadID : Type where [external]

%foreign "C:idris2_isNull, libidris2_support, idris_support.h"
         "javascript:lambda:x=>x===undefined||x===null?1:0"
export
prim__nullAnyPtr : AnyPtr -> Int

%foreign "C:idris2_getNull, libidris2_support, idris_support.h"
export
prim__getNullAnyPtr : AnyPtr

export
prim__castPtr : AnyPtr -> Ptr t
prim__castPtr = believe_me

export
prim__forgetPtr : Ptr t -> AnyPtr
prim__forgetPtr = believe_me

export %inline
prim__nullPtr : Ptr t -> Int -- can't pass 'type' to a foreign function
prim__nullPtr p = prim__nullAnyPtr (prim__forgetPtr p)
