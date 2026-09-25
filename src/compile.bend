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

# A mapping entry lives at keccak256(key . base), as in Solidity.
def loc(l: IR.Loc) -> String:
  match l:
    case IR.Plain{slot}:
      atom(slot)
    case IR.Mapped{base, key}:
      call("mapped", [loc(base), atom(key)])

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
    case Yul.Select{cond, yes, no}:
      c y n = exp(cond) exp(yes) exp(no)
      call("select", [c, y, n])
    case Yul.Timestamp{}:
      "timestamp()"
    case Yul.ChainId{}:
      "chainid()"
    case Yul.Address{}:
      "address()"
    case Yul.Keccak{words}:
      call("keccak256", ["0", nat(Nat.mul(32n, List.length(&2, IR.Expr, words)))])
    case Yul.Typed{domain, message}:
      call("typed", [atom(domain), atom(message)])
    case Yul.Id{text}:
      Keccak.digest(text)
    case Yul.Recover{digest, v, r, sig}:
      call("recover", [atom(digest), atom(v), atom(r), atom(sig)])

def atoms(exprs: List<&2, IR.Expr>) -> List<&2, String>:
  match exprs:
    case Nil{}:
      Nil{}
    case e <> rest:
      atom(e) <> atoms(rest)

def revert() -> String:
  "revert(0, 0)"

# Log data word i goes to memory at 32 * i.
def stores(+pad: String, data: List<&2, IR.Expr>, +offset: Nat) -> String:
  match data:
    case Nil{}:
      ""
    case d <> rest:
      pad ++ call("mstore", [nat(offset), atom(d)]) ++ "\n" ++ stores(pad, rest, Nat.add(32n, offset))

# keccak256 of words reads them from memory at 0, so they are stored first.
def prelude(+pad: String, value: Yul.Exp) -> String:
  match value:
    case Yul.Keccak{words}:
      stores(pad, words, 0n)
    case _:
      ""

# halt is the text for a final stop: stop() in the runtime code, nothing in
# the deploy code.
def stmt(+pad: String, +halt: String, s: Yul.Stmt) -> String:
  match s:
    case Yul.Let{level, +value, body}:
      prelude(pad, value) ++ pad ++ "let " ++ var(level) ++ " := " ++ exp(value) ++ "\n" ++ stmt(pad, halt, body)
    case Yul.SStore{l, value, body}:
      pad ++ call("sstore", [loc(l), exp(value)]) ++ "\n" ++ stmt(pad, halt, body)
    case Yul.Log{event, +topics, +data, body}:
      +n = Nat.add(1n, List.length(&2, IR.Expr, topics))
      +size = Nat.mul(32n, List.length(&2, IR.Expr, data))
      stores(pad, data, 0n)
        ++ pad ++ call("log" ++ nat(n), "0" <> nat(size) <> Keccak.digest(event) <> atoms(topics)) ++ "\n"
        ++ stmt(pad, halt, body)
    case Yul.Check{cond, body}:
      pad ++ "if " ++ exp(cond) ++ " { " ++ revert() ++ " }\n" ++ stmt(pad, halt, body)
    case Yul.Result{+value}:
      prelude(pad, value) ++ pad ++ "mstore(0, " ++ exp(value) ++ ")\n" ++ pad ++ "return(0, 32)\n"
    case Yul.Stop{}:
      halt
    case Yul.Revert{}:
      pad ++ revert() ++ "\n"

# An address argument must fit in 160 bits.
def range(+pad: String, typ: String, +level: Nat) -> String:
  match typ:
    case "address":
      pad ++ "if shr(160, " ++ var(level) ++ ") { " ++ revert() ++ " }\n"
    case "uint8":
      pad ++ "if gt(" ++ var(level) ++ ", 255) { " ++ revert() ++ " }\n"
    case "bool":
      pad ++ "if gt(" ++ var(level) ++ ", 1) { " ++ revert() ++ " }\n"
    case _:
      ""

# Parameter i has level i and is the ABI word at base + 32 * i, read with
# load: calldataload in the runtime, mload of the copied arguments in init.
def parameters(+pad: String, +load: String, +base: Nat, types: List<&2, String>, +level: Nat) -> String:
  match types:
    case Nil{}:
      ""
    case +typ <> rest:
      +offset = Nat.add(base, Nat.mul(32n, level))
      pad ++ "let " ++ var(level) ++ " := " ++ load ++ "(" ++ nat(offset) ++ ")\n" ++ range(pad, typ, level)
        ++ parameters(pad, load, base, rest, Nat.add(1n, level))

type Function is Data:
  Function{name: String, parameters: List<&2, Nat>, types: List<&2, String>, body: IR.Cmd}

def indent() -> String:
  "        "

def branch.text(+signature: String, +types: List<&2, String>, body: Yul.Stmt) -> String:
  +pad = indent()
  +size = Nat.add(4n, Nat.mul(32n, List.length(&2, String, types)))
  "      case " ++ Keccak.hex(Keccak.selector(signature)) ++ " {\n"
    ++ pad ++ "if lt(calldatasize(), " ++ nat(size) ++ ") { " ++ revert() ++ " }\n"
    ++ parameters(pad, "calldataload", 4n, types, 0n) ++ stmt(pad, pad ++ "stop()\n", body) ++ "      }\n"

# The model keeps a plain slot apart from every mapping entry. On chain that
# holds only when the slot is fixed: a slot from a variable could be
# keccak256(key . base) and alias an entry. So every plain slot and mapping
# base must be a literal. Keys may be variables.
def fixed.loc(l: IR.Loc) -> Bool:
  match l:
    case IR.Plain{IR.Lit{_}}:
      True{}
    case IR.Plain{IR.Var{_}}:
      False{}
    case IR.Mapped{base, _}:
      fixed.loc(base)

def fixed(cmd: IR.Cmd) -> Bool:
  match cmd:
    case IR.Bind{IR.SLoad{l}, _, body}:
      Bool.and(fixed.loc(l), fixed(body))
    case IR.Bind{_, _, body}:
      fixed(body)
    case IR.Then{IR.SStore{l, _}, body}:
      Bool.and(fixed.loc(l), fixed(body))
    case IR.Then{_, body}:
      fixed(body)
    case IR.Tail{IR.SLoad{l}}:
      fixed.loc(l)
    case IR.Finish{IR.SStore{l, _}}:
      fixed.loc(l)
    case _:
      True{}

# An entry compiles only if its variables are bound and its slots are fixed.
def valid(+body: IR.Cmd, +levels: List<&2, Nat>) -> Bool:
  Bool.and(IR.closed(body, levels), fixed(body))

def branch.closed(+signature: String, +types: List<&2, String>, +levels: List<&2, Nat>, +body: IR.Cmd) ->
  Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, valid(body, levels),
    Done{branch.text(signature, types, Yul.lower(body, Read.output(body)))},
    Fail{signature ++ ": the IR has an unbound variable or a storage slot that is not a literal"})

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

def zeros(+n: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+(+p):
      "00" ++ zeros(p)

# The first n bytes of s in hex, zero-padded on the right.
def word.hex(+n: Nat, s: String) -> String:
  match n s:
    case 0n _:
      ""
    case +m SNil{}:
      zeros(m)
    case 1n+(+p) SCon{c, rest}:
      Keccak.hex.byte(Char.to_u32(c)) ++ word.hex(p, rest)

# One mstore for each 32 bytes of s, from offset on. Fuel is s's length.
def mstores(+fuel: Nat, +pad: String, s: String, +offset: Nat) -> String:
  match fuel s:
    case 0n _:
      ""
    case _ SNil{}:
      ""
    case 1n+(+f) +t:
      pad ++ "mstore(" ++ nat(offset) ++ ", 0x" ++ word.hex(32n, t) ++ ")\n"
        ++ mstores(f, pad, String.drop(t, 32n), Nat.add(offset, 32n))

def ascii(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, rest}:
      Bool.and(Nat.is_lt(U32.to_nat(Char.to_u32(c)), 128n), ascii(rest))

# A constant string entry returns the ABI encoding of its text: the offset
# 32, the length, and the bytes in 32-byte words, zero-padded on the right.
def constant.text(+name: String, +value: String) -> String:
  +pad = indent()
  +size = String.length(value)
  "      case " ++ Keccak.hex(Keccak.selector(name ++ "()")) ++ " {\n"
    ++ pad ++ "mstore(0, 32)\n" ++ pad ++ "mstore(32, " ++ nat(size) ++ ")\n"
    ++ mstores(size, pad, value, 64n)
    ++ pad ++ "return(0, " ++ nat(Nat.add(64n, Nat.mul(32n, Nat.div(Nat.add(size, 31n), 32n)))) ++ ")\n      }\n"

def constant.ascii(+name: String, +value: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, ascii(value), Done{constant.text(name, value)},
    Fail{name ++ ": a constant string must be ASCII"})

def constant(+name: String, +value: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, Keccak.fits(name ++ "()"), constant.ascii(name, value),
    Fail{name ++ "(): signatures over 135 bytes are not supported"})

def case.text(+name: String, found: Maybe<&2, String>, +evm: String, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, String>:
  match found:
    case Some{value}:
      constant(name, value)
    case None{}:
      do Result<&2, &2, String, String>:
        entry : Read.Entry <- Read.entry(evm, decls, name)
        types : List<&2, String> <- Read.types(evm, decls, name)
        f : Function <- function(name, entry, types)
        branch(f)

def cases(names: List<&2, String>, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, String>:
  match names:
    case Nil{}:
      Done{""}
    case +name <> rest:
      do Result<&2, &2, String, String>:
        head : String <- case.text(name, Read.string_entry(decls, name), evm, decls)
        tail : String <- cases(rest, evm, decls)
        return head ++ tail

# Yul functions that lowered code calls. Each code block defines its own.
def helpers(+pad: String) -> String:
  pad ++ "function mapped(slot, key) -> location {\n"
    ++ pad ++ "  mstore(0, key)\n"
    ++ pad ++ "  mstore(32, slot)\n"
    ++ pad ++ "  location := keccak256(0, 64)\n"
    ++ pad ++ "}\n"
    ++ pad ++ "function select(c, a, b) -> v {\n"
    ++ pad ++ "  v := b\n"
    ++ pad ++ "  if c { v := a }\n"
    ++ pad ++ "}\n"
    ++ pad ++ "function typed(domain, message) -> digest {\n"
    ++ pad ++ "  mstore(0, 0x1901000000000000000000000000000000000000000000000000000000000000)\n"
    ++ pad ++ "  mstore(2, domain)\n"
    ++ pad ++ "  mstore(34, message)\n"
    ++ pad ++ "  digest := keccak256(0, 66)\n"
    ++ pad ++ "}\n"
    ++ pad ++ "function recover(digest, v, r, s) -> signer {\n"
    ++ pad ++ "  mstore(0, digest)\n"
    ++ pad ++ "  mstore(32, v)\n"
    ++ pad ++ "  mstore(64, r)\n"
    ++ pad ++ "  mstore(96, s)\n"
    ++ pad ++ "  mstore(128, 0)\n"
    ++ pad ++ "  pop(staticcall(gas(), 1, 0, 128, 128, 32))\n"
    ++ pad ++ "  signer := mload(128)\n"
    ++ pad ++ "}\n"

def object(init: String, body: String) -> String:
  "object \"Contract\" {\n"
    ++ "  code {\n"
    ++ helpers("    ")
    ++ "    if callvalue() { " ++ revert() ++ " }\n"
    ++ init
    ++ "    datacopy(0, dataoffset(\"runtime\"), datasize(\"runtime\"))\n"
    ++ "    return(0, datasize(\"runtime\"))\n"
    ++ "  }\n"
    ++ "  object \"runtime\" {\n"
    ++ "    code {\n"
    ++ helpers("      ")
    ++ "      if callvalue() { " ++ revert() ++ " }\n"
    ++ "      if lt(calldatasize(), 4) { " ++ revert() ++ " }\n"
    ++ "      switch shr(224, calldataload(0))\n"
    ++ body
    ++ "      default { " ++ revert() ++ " }\n"
    ++ "    }\n"
    ++ "  }\n"
    ++ "}\n"

# An entry named init is the constructor. It runs in the deploy code, where a
# final stop falls through to returning the runtime code.
def is_init(+name: String) -> Bool:
  match name:
    case "init":
      True{}
    case _:
      False{}

def has_init(names: List<&2, String>) -> Bool:
  match names:
    case Nil{}:
      False{}
    case +name <> rest:
      Bool.or(is_init(name), has_init(rest))

def without_init(names: List<&2, String>) -> List<&2, String>:
  match names:
    case Nil{}:
      Nil{}
    case +name <> rest:
      +kept = without_init(rest)
      Bool.pick(List<&2, String>, is_init(name), kept, name <> kept)

# Constructor arguments are ABI words after the deploy code. They are copied
# to memory and read before the body runs, which uses memory for mapped().
def arguments(types: List<&2, String>) -> String:
  match types:
    case Nil{}:
      ""
    case +typ <> +rest:
      +size = nat(Nat.mul(32n, List.length(&2, String, typ <> rest)))
      "    if lt(sub(codesize(), datasize(\"Contract\")), " ++ size ++ ") { " ++ revert() ++ " }\n"
        ++ "    codecopy(0, datasize(\"Contract\"), " ++ size ++ ")\n"
        ++ parameters("    ", "mload", 0n, typ <> rest, 0n)

def init.stops(out: IR.Output, +body: IR.Cmd, +levels: List<&2, Nat>, types: List<&2, String>) ->
  Result<&2, &2, String, String>:
  match out:
    case IR.Stops{}:
      Bool.pick(Result<&2, &2, String, String>, valid(body, levels),
        Done{arguments(types) ++ stmt("    ", "", Yul.lower(body, IR.Stops{}))},
        Fail{"init: the IR has an unbound variable or a storage slot that is not a literal"})
    case IR.Returns{}:
      Fail{"init must return Unit"}

def init.text(entry: Read.Entry, +types: List<&2, String>) -> Result<&2, &2, String, String>:
  match entry:
    case Read.Entry{+levels, +body}:
      Bool.pick(Result<&2, &2, String, String>, Certify.numbered(levels, 0n),
        init.stops(Read.output(body), body, levels, types),
        Fail{"init: parameter levels are not 0, 1, ..."})

def constructor(found: Bool, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, String>:
  match found:
    case True{}:
      do Result<&2, &2, String, String>:
        entry : Read.Entry <- Read.entry(evm, decls, "init")
        types : List<&2, String> <- Read.types(evm, decls, "init")
        init.text(entry, types)
    case False{}:
      Done{""}

def contract(program: Core.Program, +backend: String, entries: List<&2, String>) -> Result<&2, &2, String, String>:
  match program entries:
    case Core.Program{_, _, _, _, entry, _, _, _, +decls, _} +first <> +rest:
      do Result<&2, &2, String, String>:
        leading : String <- Read.contract.first(first <> rest, decls)
        prefix : String <- Read.prefix(decls, leading)
        +evm : String <- Certify.module(entry, prefix, backend)
        init : String <- constructor(has_init(first <> rest), evm, decls)
        body : String <- cases(without_init(first <> rest), evm, decls)
        return object(init, body)
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
