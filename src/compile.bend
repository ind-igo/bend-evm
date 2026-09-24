import Base
import ../vendor/bend-frontend/src/core.bend as Core
import ../vendor/bend-frontend/src/frontend.bend as Frontend
import ./ir.bend as IR
import ./read.bend as Read
import ./yul.bend as Yul
import ./keccak.bend as Keccak
import ./certify.bend as Certify

# Prints a Yul object for the named contract functions, with an ABI
# dispatcher. Parameters and results are uint256.
# Usage: compile.bend <contract.bend> <function>...

def nat(n: Nat) -> String:
  Nat.show(n)

def var(level: Nat) -> String:
  "v" ++ nat(level)

def atom(e: IR.Expr) -> String:
  match e:
    case IR.Lit{value}:
      nat(value)
    case IR.Var{level}:
      var(level)

def call(name: String, args: List<&2, String>) -> String:
  name ++ "(" ++ String.join(args, ", ") ++ ")"

def exp(e: Yul.Exp) -> String:
  match e:
    case Yul.Atom{value}:
      atom(value)
    case Yul.SLoad{key}:
      call("sload", [exp(key)])
    case Yul.Caller{}:
      "caller()"
    case Yul.Add{left, right}:
      a b = exp(left) exp(right)
      call("add", [a, b])
    case Yul.Sub{left, right}:
      a b = exp(left) exp(right)
      call("sub", [a, b])
    case Yul.Not{value}:
      call("not", [exp(value)])
    case Yul.Eq{left, right}:
      a b = exp(left) exp(right)
      call("eq", [a, b])
    case Yul.Lt{left, right}:
      a b = exp(left) exp(right)
      call("lt", [a, b])
    case Yul.Gt{left, right}:
      a b = exp(left) exp(right)
      call("gt", [a, b])
    case Yul.IsZero{value}:
      call("iszero", [exp(value)])

def revert() -> String:
  "revert(0, 0)"

def stmt(+pad: String, s: Yul.Stmt) -> String:
  match s:
    case Yul.Let{level, value, body}:
      pad ++ "let " ++ var(level) ++ " := " ++ exp(value) ++ "\n" ++ stmt(pad, body)
    case Yul.SStore{key, value, body}:
      pad ++ call("sstore", [exp(key), exp(value)]) ++ "\n" ++ stmt(pad, body)
    case Yul.Check{cond, body}:
      pad ++ "if " ++ exp(cond) ++ " { " ++ revert() ++ " }\n" ++ stmt(pad, body)
    case Yul.Result{value}:
      pad ++ "mstore(0, " ++ exp(value) ++ ")\n" ++ pad ++ "return(0, 32)\n"
    case Yul.Stop{}:
      pad ++ "stop()\n"
    case Yul.Revert{}:
      pad ++ revert() ++ "\n"

# Parameter i is the ABI word at 4 + 32 * i.
def parameters(+pad: String, levels: List<&2, Nat>) -> String:
  match levels:
    case Nil{}:
      ""
    case +level <> rest:
      +offset = Nat.add(4n, Nat.mul(32n, level))
      pad ++ "let " ++ var(level) ++ " := calldataload(" ++ nat(offset) ++ ")\n" ++ parameters(pad, rest)

def uints(levels: List<&2, Nat>) -> List<&2, String>:
  match levels:
    case Nil{}:
      Nil{}
    case _ <> rest:
      "uint256" <> uints(rest)

type Function is Data:
  Function{name: String, parameters: List<&2, Nat>, body: IR.Cmd}

def indent() -> String:
  "        "

def branch.text(+signature: String, +levels: List<&2, Nat>, body: Yul.Stmt) -> String:
  +pad = indent()
  +size = Nat.add(4n, Nat.mul(32n, List.length(&2, Nat, levels)))
  "      case " ++ Keccak.hex(Keccak.selector(signature)) ++ " {\n"
    ++ pad ++ "if lt(calldatasize(), " ++ nat(size) ++ ") { " ++ revert() ++ " }\n"
    ++ parameters(pad, levels) ++ stmt(pad, body) ++ "      }\n"

def branch.closed(+signature: String, +levels: List<&2, Nat>, +body: IR.Cmd) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, IR.closed(body, levels),
    Done{branch.text(signature, levels, Yul.lower(body, Read.output(body)))},
    Fail{signature ++ ": the IR has an unbound variable"})

def branch(f: Function) -> Result<&2, &2, String, String>:
  match f:
    case Function{name, +levels, body}:
      +signature = call(name, uints(levels))
      Bool.pick(Result<&2, &2, String, String>, Keccak.fits(signature),
        branch.closed(signature, levels, body),
        Fail{signature ++ ": signatures over 135 bytes are not supported"})

def function(+name: String, entry: Read.Entry) -> Result<&2, &2, String, Function>:
  match entry:
    case Read.Entry{+levels, body}:
      Bool.pick(Result<&2, &2, String, Function>, Certify.numbered(levels, 0n),
        Done{Function{name, levels, body}},
        Fail{name ++ ": parameter levels are not 0, 1, ..."})

def cases(names: List<&2, String>, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, String>:
  match names:
    case Nil{}:
      Done{""}
    case +name <> rest:
      do Result<&2, &2, String, String>:
        entry : Read.Entry <- Read.entry(evm, decls, name)
        f : Function <- function(name, entry)
        head : String <- branch(f)
        tail : String <- cases(rest, evm, decls)
        return head ++ tail

def object(body: String) -> String:
  "object \"Contract\" {\n"
    ++ "  code {\n"
    ++ "    datacopy(0, dataoffset(\"runtime\"), datasize(\"runtime\"))\n"
    ++ "    return(0, datasize(\"runtime\"))\n"
    ++ "  }\n"
    ++ "  object \"runtime\" {\n"
    ++ "    code {\n"
    ++ "      if callvalue() { " ++ revert() ++ " }\n"
    ++ "      if lt(calldatasize(), 4) { " ++ revert() ++ " }\n"
    ++ "      switch shr(224, calldataload(0))\n"
    ++ body
    ++ "      default { " ++ revert() ++ " }\n"
    ++ "    }\n"
    ++ "  }\n"
    ++ "}\n"

def contract(program: Core.Program, +backend: String, entries: List<&2, String>) -> Result<&2, &2, String, String>:
  match program entries:
    case Core.Program{_, _, _, _, entry, _, _, _, +decls, _} +first <> rest:
      do Result<&2, &2, String, String>:
        prefix : String <- Read.prefix(decls, first)
        evm : String <- Certify.module(entry, prefix, backend)
        body : String <- cases(first <> rest, evm, decls)
        return object(body)
    case _ Nil{}:
      Fail{"Name at least one contract function"}

def run(file: String, entries: List<String>) -> IO(Unit):
  do IO<Unit>:
    # host/run.js sets BEND_ENTRY to this file's real path.
    found : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_ENTRY")
    backend : String <- IO.pass(String, found)
    result : Result<&2, &2, String, Core.Program> <- Frontend.check(file)
    program : Core.Program <- Frontend.or_die(Core.Program, result)
    text : String <- Frontend.or_die(String, contract(program, backend, Certify.strings(entries)))
    IO.write(text)

def args(values: List<String>) -> IO(Unit):
  match values:
    case file <> entries:
      run(file, entries)
    case Nil{}:
      IO.die(Unit, 1, "Usage: compile.bend <contract.bend> <function>...")

def main() -> IO(Unit):
  do IO<Unit>:
    values : List<String> <- IO.args()
    args(values)
