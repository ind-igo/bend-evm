import Base
import ../vendor/bend-frontend/src/core.bend as Core
import ../vendor/bend-frontend/src/frontend.bend as Frontend
import ./ir.bend as IR
import ./read.bend as Read
import ./yul.bend as Yul
import ./keccak.bend as Keccak
import ./certify.bend as Certify

# Prints a Yul object for the named contract functions, with an ABI
# dispatcher. Parameters are uint256 or address; results are uint256.
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

# A mapping entry lives at keccak256(key . slot), as in Solidity.
def loc(l: IR.Loc) -> String:
  match l:
    case IR.Plain{slot}:
      atom(slot)
    case IR.Mapped{slot, key}:
      call("mapped", [atom(slot), atom(key)])

def exp(e: Yul.Exp) -> String:
  match e:
    case Yul.Atom{value}:
      atom(value)
    case Yul.SLoad{l}:
      call("sload", [loc(l)])
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

def atoms(exprs: List<&2, IR.Expr>) -> List<&2, String>:
  match exprs:
    case Nil{}:
      Nil{}
    case e <> rest:
      atom(e) <> atoms(rest)

def revert() -> String:
  "revert(0, 0)"

def stmt(+pad: String, s: Yul.Stmt) -> String:
  match s:
    case Yul.Let{level, value, body}:
      pad ++ "let " ++ var(level) ++ " := " ++ exp(value) ++ "\n" ++ stmt(pad, body)
    case Yul.SStore{l, value, body}:
      pad ++ call("sstore", [loc(l), exp(value)]) ++ "\n" ++ stmt(pad, body)
    case Yul.Log{event, +topics, data, body}:
      +n = Nat.add(1n, List.length(&2, IR.Expr, topics))
      pad ++ "mstore(0, " ++ exp(data) ++ ")\n"
        ++ pad ++ call("log" ++ nat(n), "0" <> "32" <> Keccak.digest(event) <> atoms(topics)) ++ "\n" ++ stmt(pad, body)
    case Yul.Check{cond, body}:
      pad ++ "if " ++ exp(cond) ++ " { " ++ revert() ++ " }\n" ++ stmt(pad, body)
    case Yul.Result{value}:
      pad ++ "mstore(0, " ++ exp(value) ++ ")\n" ++ pad ++ "return(0, 32)\n"
    case Yul.Stop{}:
      pad ++ "stop()\n"
    case Yul.Revert{}:
      pad ++ revert() ++ "\n"

# An address argument must fit in 160 bits.
def range(+pad: String, typ: String, +level: Nat) -> String:
  match typ:
    case "address":
      pad ++ "if shr(160, " ++ var(level) ++ ") { " ++ revert() ++ " }\n"
    case _:
      ""

# Parameter i has level i and is the ABI word at 4 + 32 * i.
def parameters(+pad: String, types: List<&2, String>, +level: Nat) -> String:
  match types:
    case Nil{}:
      ""
    case +typ <> rest:
      +offset = Nat.add(4n, Nat.mul(32n, level))
      pad ++ "let " ++ var(level) ++ " := calldataload(" ++ nat(offset) ++ ")\n" ++ range(pad, typ, level)
        ++ parameters(pad, rest, Nat.add(1n, level))

type Function is Data:
  Function{name: String, parameters: List<&2, Nat>, types: List<&2, String>, body: IR.Cmd}

def indent() -> String:
  "        "

def branch.text(+signature: String, +types: List<&2, String>, body: Yul.Stmt) -> String:
  +pad = indent()
  +size = Nat.add(4n, Nat.mul(32n, List.length(&2, String, types)))
  "      case " ++ Keccak.hex(Keccak.selector(signature)) ++ " {\n"
    ++ pad ++ "if lt(calldatasize(), " ++ nat(size) ++ ") { " ++ revert() ++ " }\n"
    ++ parameters(pad, types, 0n) ++ stmt(pad, body) ++ "      }\n"

def branch.closed(+signature: String, +types: List<&2, String>, +levels: List<&2, Nat>, +body: IR.Cmd) ->
  Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, IR.closed(body, levels),
    Done{branch.text(signature, types, Yul.lower(body, Read.output(body)))},
    Fail{signature ++ ": the IR has an unbound variable"})

def branch(f: Function) -> Result<&2, &2, String, String>:
  match f:
    case Function{name, +levels, +types, body}:
      +signature = name ++ "(" ++ String.join(types, ",") ++ ")"
      Bool.pick(Result<&2, &2, String, String>, Keccak.fits(signature),
        branch.closed(signature, types, levels, body),
        Fail{signature ++ ": signatures over 135 bytes are not supported"})

def function(+name: String, entry: Read.Entry, types: List<&2, String>) -> Result<&2, &2, String, Function>:
  match entry:
    case Read.Entry{+levels, body}:
      Bool.pick(Result<&2, &2, String, Function>, Certify.numbered(levels, 0n),
        Done{Function{name, levels, types, body}},
        Fail{name ++ ": parameter levels are not 0, 1, ..."})

def cases(names: List<&2, String>, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, String>:
  match names:
    case Nil{}:
      Done{""}
    case +name <> rest:
      do Result<&2, &2, String, String>:
        entry : Read.Entry <- Read.entry(evm, decls, name)
        types : List<&2, String> <- Read.types(evm, decls, name)
        f : Function <- function(name, entry, types)
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
    ++ "      function mapped(slot, key) -> location {\n"
    ++ "        mstore(0, key)\n"
    ++ "        mstore(32, slot)\n"
    ++ "        location := keccak256(0, 64)\n"
    ++ "      }\n"
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
