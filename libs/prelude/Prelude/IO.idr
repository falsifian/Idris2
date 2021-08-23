module Prelude.IO

import Builtin
import PrimIO
import Prelude.Basics
import Prelude.Interfaces
import Prelude.Show

%default total

--------
-- IO --
--------

data IORes1 : Type -> Type where
     MkIORes1 : (1 result : a) -> (1 x : %World) -> IORes1 a

-- This IO implementation is designed to take advantage of tail recursion. If
-- at some point the compiler supports tail calls more generally, this can
-- probably be simplified to a simple wrapper around PrimIO.
export
data IO : Type -> Type where
  Return : a -> IO a
  Continue : (1 fn : (1 x : %World) -> IORes1 (IO a)) -> IO a

export %inline
fromPrim : (1 fn : (1 x : %World) -> IORes a) -> IO a
fromPrim op =
  Continue
  (\w => let MkIORes x w' = op w in MkIORes1 (Return x) w')

export
toPrim : (1 act : IO a) -> PrimIO a
toPrim (Return x) w = MkIORes x w
toPrim (Continue x) w =
  let MkIORes1 x' w' = x w
  in toPrim x' w'

%inline
export
io_pure : a -> IO a
io_pure = Return

-- There's a special case for inlining this is Compiler.Inline, because
-- the inliner is cautious about case blocks at the moment. Once it's less
-- cautious, add an explicit %inline directive and take out the special case.
-- See also dealing with the newtype optimisation via %World in
-- Compiler.CompileExpr
export
io_bind : (1 act : IO a) -> (1 k : a -> IO b) -> IO b
io_bind (Return x) k = k x
io_bind (Continue x) k =
  Continue
  (\w => let MkIORes1 x' w' = x w in MkIORes1 (io_bind x' k) w')

public export
Functor IO where
  map f io = io_bind io $ io_pure . f

%inline
public export
Applicative IO where
  pure x = io_pure x
  f <*> a
      = io_bind f (\f' =>
          io_bind a (\a' =>
            io_pure (f' a')))

%inline
public export
Monad IO where
  b >>= k = io_bind b k

public export
interface Monad io => HasIO io where
  constructor MkHasIO
  liftIO : IO a -> io a

public export
interface Monad io => HasLinearIO io where
  constructor MkHasLinearIO
  liftIO1 : (1 _ : IO a) -> io a

public export %inline
HasLinearIO IO where
  liftIO1 x = x

public export %inline
HasLinearIO io => HasIO io where
  liftIO x = liftIO1 x

export %inline
primIO : HasIO io => (fn : (1 x : %World) -> IORes a) -> io a
primIO op = liftIO (fromPrim op)

export %inline
primIO1 : HasLinearIO io => (1 fn : (1 x : %World) -> IORes a) -> io a
primIO1 op = liftIO1 (fromPrim op)

%extern
prim__onCollectAny : AnyPtr -> (AnyPtr -> PrimIO ()) -> PrimIO GCAnyPtr
%extern
prim__onCollect : Ptr t -> (Ptr t -> PrimIO ()) -> PrimIO (GCPtr t)

export
onCollectAny : HasIO io => AnyPtr -> (AnyPtr -> IO ()) -> io GCAnyPtr
onCollectAny ptr c = primIO (prim__onCollectAny ptr (\x => toPrim (c x)))

export
onCollect : HasIO io => Ptr t -> (Ptr t -> IO ()) -> io (GCPtr t)
onCollect ptr c = primIO (prim__onCollect ptr (\x => toPrim (c x)))

%foreign "C:idris2_getString, libidris2_support, idris_support.h"
         "javascript:lambda:x=>x"
export
prim__getString : Ptr String -> String

%foreign "C:putchar,libc 6"
prim__putChar : Char -> (1 x : %World) -> IORes ()
%foreign "C:getchar,libc 6"
%extern prim__getChar : (1 x : %World) -> IORes Char

%foreign "C:idris2_getStr, libidris2_support, idris_support.h"
         "node:support:getStr,support_system_file"
prim__getStr : PrimIO String

%foreign "C:idris2_putStr, libidris2_support, idris_support.h"
         "node:lambda:x=>process.stdout.write(x)"
prim__putStr : String -> PrimIO ()

||| Output a string to stdout without a trailing newline.
export
putStr : HasIO io => String -> io ()
putStr str = primIO (prim__putStr str)

||| Output a string to stdout with a trailing newline.
export
putStrLn : HasIO io => String -> io ()
putStrLn str = putStr (prim__strAppend str "\n")

||| Read one line of input from stdin, without the trailing newline.
export
getLine : HasIO io => io String
getLine = primIO prim__getStr

||| Write one single-byte character to stdout.
export
putChar : HasIO io => Char -> io ()
putChar c = primIO (prim__putChar c)

||| Write one multi-byte character to stdout, with a trailing newline.
export
putCharLn : HasIO io => Char -> io ()
putCharLn c = putStrLn (prim__cast_CharString c)

||| Read one single-byte character from stdin.
export
getChar : HasIO io => io Char
getChar = primIO prim__getChar

%foreign "scheme:blodwen-thread"
export
prim__fork : (1 prog : PrimIO ()) -> PrimIO ThreadID

export
fork : (1 prog : IO ()) -> IO ThreadID
fork act = fromPrim (prim__fork (toPrim act))

%foreign "scheme:blodwen-thread-wait"
export
prim__threadWait : (1 threadID : ThreadID) -> PrimIO ()

export
threadWait : (1 threadID : ThreadID) -> IO ()
threadWait threadID = fromPrim (prim__threadWait threadID)

||| Output something showable to stdout, without a trailing newline.
export
print : (HasIO io, Show a) => a -> io ()
print x = putStr $ show x

||| Output something showable to stdout, with a trailing newline.
export
printLn : (HasIO io, Show a) => a -> io ()
printLn x = putStrLn $ show x

unsafeCreateWorld : (1 f : (1 x : %World) -> a) -> a
unsafeCreateWorld f = f %MkWorld

unsafeDestroyWorld : (1 x : %World) -> a -> a
unsafeDestroyWorld %MkWorld x = x

unsafePerformPrimIO : PrimIO a -> a
unsafePerformPrimIO f
    = unsafeCreateWorld (\w => case f w of
                               MkIORes res w' => unsafeDestroyWorld w' res)

export
unsafePerformIO : IO a -> a
unsafePerformIO x = unsafePerformPrimIO (toPrim x)
