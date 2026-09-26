import Base
import ../vendor/bend-frontend/src/core.bend as Core
import ../vendor/bend-frontend/src/frontend.bend as Frontend
import ./read.bend as Read

# What certify.bend, compile.bend and abi.bend share: the command line, and
# reading the named entries once from a contract that imports this
# backend's Evm.bend.

def otherwise(fallback: String, value: Maybe<&2, String>) -> String:
  match value:
    case Some{s}:
      s
    case None{}:
      fallback

# The Evm module's path, such as "../Evm", from its name prefix "../Evm.".
def evm.path(+evm: String) -> String:
  otherwise(evm, Read.before(".", evm))

# A path without its last segment.
def parent.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      Bool.pick(String, Char.is_eq(c, '/'), rest, parent.go(rest))

def parent(path: String) -> String:
  String.reverse(parent.go(String.reverse(path)))

# Upstream namespaces are normalized: leading ".." segments, then names.
def resolve(segments: List<&2, String>, +dir: String) -> String:
  match segments:
    case Nil{}:
      dir
    case +segment <> rest:
      resolve(rest, Bool.pick(String, String.eq(segment, ".."), parent(dir),
        Bool.pick(String, String.is_empty(segment), dir, dir ++ "/" ++ segment)))

# The file that the contract's Evm namespace, such as "../Evm", names.
def module.file(entry: String, +namespace: String) -> String:
  dir = Bool.pick(String, String.starts_with(namespace, "/"), "", parent(entry))
  resolve(String.split(namespace, '/'), dir) ++ ".bend"

# A certificate imports Evm.bend and ir.bend beside the contract's Evm
# module, so that module must be this backend's own Evm.bend.
def module(entry: String, +evm: String, +backend: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>,
    String.eq(module.file(entry, evm.path(evm)), parent(backend) ++ "/Evm.bend"),
    Done{evm},
    Fail{"The contract must import this backend's Evm.bend"})

# The Evm module's name prefix, each named entry, read once, and the
# declarations.
type Setup is Data:
  Setup{evm: String, functions: List<&2, Read.Function>, decls: List<&2, Core.Declaration>}

def setup(program: Core.Program, +backend: String, +entries: List<&2, String>) -> Result<&2, &2, String, Setup>:
  match program:
    case Core.Program{_, _, _, _, entry, _, _, _, +decls, _}:
      do Result<&2, &2, String, Setup>:
        prefix : String <- Read.module(decls, entries)
        +evm : String <- module(entry, prefix, backend)
        fs : List<&2, Read.Function> <- Read.functions(evm, decls, entries)
        return Setup{evm, fs, decls}

def strings(values: List<String>) -> List<&2, String>:
  match values:
    case Nil{}:
      Nil{}
    case value <> rest:
      value <> strings(rest)

def made(~make: String -> Setup -> Result<&2, &2, String, String>, +file: String, program: Core.Program,
  +backend: String, entries: List<&2, String>) -> Result<&2, &2, String, String>:
  do Result<&2, &2, String, String>:
    s : Setup <- setup(program, backend, entries)
    make(file, s)

def run(~make: String -> Setup -> Result<&2, &2, String, String>, +file: String, entries: List<String>) -> IO(Unit):
  do IO<Unit>:
    # host/run.js sets BEND_ENTRY to the tool's real path.
    found : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_ENTRY")
    backend : String <- IO.pass(String, found)
    result : Result<&2, &2, String, Core.Program> <- Frontend.check(file)
    program : Core.Program <- Frontend.or_die(Core.Program, result)
    text : String <- Frontend.or_die(String, made(~make, file, program, backend, strings(entries)))
    IO.write(text)

def args(~make: String -> Setup -> Result<&2, &2, String, String>, usage: String, values: List<String>) -> IO(Unit):
  match values:
    case +file <> entries:
      run(~make, file, entries)
    case Nil{}:
      IO.die(Unit, 1, usage)

# A tool's main: make gets the contract's file and its setup, and gives the
# text to print.
def main(~make: String -> Setup -> Result<&2, &2, String, String>, usage: String) -> IO(Unit):
  do IO<Unit>:
    values : List<String> <- IO.args()
    args(~make, usage, values)
