import Base
import ./ir.bend as IR
import ./read.bend as Read
import ./yul.bend as Yul
import ./keccak.bend as Keccak
import ./tool.bend as Tool

# Prints a Yul object for the named entries, with an ABI dispatcher. The
# dispatcher range-checks address, uint8 and bool parameters; results go out
# as they are. An entry named init is the constructor.
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
    case Yul.If{test, yes, no}:
      pad ++ "switch " ++ exp(test) ++ "\n" ++ pad ++ "case 0 {\n" ++ stmt(pad, halt, no) ++ pad ++ "}\n"
        ++ pad ++ "default {\n" ++ stmt(pad, halt, yes) ++ pad ++ "}\n"

# The check that rejects an argument out of its ABI type's range, if any.
def range.test(+typ: String, +v: String) -> String:
  Bool.pick(String, String.eq(typ, "address"), "shr(160, " ++ v ++ ")",
    Bool.pick(String, String.eq(typ, "uint8"), "gt(" ++ v ++ ", 255)",
      Bool.pick(String, String.eq(typ, "bool"), "gt(" ++ v ++ ", 1)", "")))

def range(+pad: String, +typ: String, +level: Nat) -> String:
  +test = range.test(typ, var(level))
  Bool.pick(String, String.is_empty(test), "", pad ++ "if " ++ test ++ " { " ++ revert() ++ " }\n")

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

def types(inputs: List<&2, Read.Input>) -> List<&2, String>:
  match inputs:
    case Nil{}:
      Nil{}
    case Read.Input{_, t} <> rest:
      t <> types(rest)

def indent() -> String:
  "        "

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
    case IR.If{_, yes, no}:
      Bool.and(fixed(yes), fixed(no))
    case _:
      True{}

# An entry compiles only if its variables are bound and its slots are fixed.
def valid(+name: String, +body: IR.Cmd, +levels: List<&2, Nat>) -> Result<&2, &2, String, IR.Cmd>:
  Bool.pick(Result<&2, &2, String, IR.Cmd>, Bool.and(IR.closed(body, levels), fixed(body)), Done{body},
    Fail{name ++ ": the IR has an unbound variable or a storage slot that is not a literal"})

# The dispatcher case of a contract function: its selector, the calldata
# size check, its parameters, then its lowered body.
def dispatch.text(+signature: String, +types: List<&2, String>, body: Yul.Stmt) -> String:
  +pad = indent()
  +size = Nat.add(4n, Nat.mul(32n, List.length(&2, String, types)))
  "      case " ++ Keccak.hex(Keccak.selector(signature)) ++ " {\n"
    ++ pad ++ "if lt(calldatasize(), " ++ nat(size) ++ ") { " ++ revert() ++ " }\n"
    ++ parameters(pad, "calldataload", 4n, types, 0n) ++ stmt(pad, pad ++ "stop()\n", body) ++ "      }\n"

def dispatch.valid(+signature: String, +types: List<&2, String>, +levels: List<&2, Nat>, +body: IR.Cmd) ->
  Result<&2, &2, String, String>:
  do Result<&2, &2, String, String>:
    +checked : IR.Cmd <- valid(signature, body, levels)
    return dispatch.text(signature, types, Yul.lower(checked, Read.output(checked)))

def dispatch(+name: String, inputs: List<&2, Read.Input>, entry: Read.Entry) -> Result<&2, &2, String, String>:
  match entry:
    case Read.Entry{+levels, +body}:
      +ts = types(inputs)
      +signature = name ++ "(" ++ String.join(ts, ",") ++ ")"
      Bool.pick(Result<&2, &2, String, String>, Keccak.fits(signature), dispatch.valid(signature, ts, levels, body),
        Fail{signature ++ ": signatures over 135 bytes are not supported"})

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
  Bool.pick(Result<&2, &2, String, String>, Keccak.ascii(value), Done{constant.text(name, value)},
    Fail{name ++ ": a constant string must be ASCII"})

def constant(+name: String, +value: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, Keccak.fits(name ++ "()"), constant.ascii(name, value),
    Fail{name ++ "(): signatures over 135 bytes are not supported"})

def case.text(f: Read.Function) -> Result<&2, &2, String, String>:
  match f:
    case Read.Constant{+name, +value}:
      constant(name, value)
    case Read.Contract{+name, inputs, _, entry}:
      dispatch(name, inputs, entry)

def is_init(f: Read.Function) -> Bool:
  match f:
    case Read.Contract{name, _, _, _}:
      String.eq(name, "init")
    case Read.Constant{_, _}:
      False{}

def cases(fs: List<&2, Read.Function>) -> Result<&2, &2, String, String>:
  match fs:
    case Nil{}:
      Done{""}
    case +f <> rest:
      do Result<&2, &2, String, String>:
        head : String <- Bool.pick(Result<&2, &2, String, String>, is_init(f), Done{""}, case.text(f))
        tail : String <- cases(rest)
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

def init.stops(out: IR.Output, inputs: List<&2, Read.Input>, +levels: List<&2, Nat>, +body: IR.Cmd) ->
  Result<&2, &2, String, String>:
  match out:
    case IR.Stops{}:
      do Result<&2, &2, String, String>:
        checked : IR.Cmd <- valid("init", body, levels)
        return arguments(types(inputs)) ++ stmt("    ", "", Yul.lower(checked, IR.Stops{}))
    case IR.Returns{}:
      Fail{"init must return Unit"}

def constructor.of(f: Read.Function) -> Result<&2, &2, String, String>:
  match f:
    case Read.Contract{_, inputs, _, Read.Entry{+levels, +body}}:
      init.stops(Read.output(body), inputs, levels, body)
    case Read.Constant{_, _}:
      Done{""}

# An entry named init is the constructor. It runs in the deploy code, where a
# final stop falls through to returning the runtime code.
def constructor(fs: List<&2, Read.Function>) -> Result<&2, &2, String, String>:
  match fs:
    case Nil{}:
      Done{""}
    case +f <> rest:
      Bool.pick(Result<&2, &2, String, String>, is_init(f), constructor.of(f), constructor(rest))

def contract(file: String, s: Tool.Setup) -> Result<&2, &2, String, String>:
  match s:
    case Tool.Setup{_, +fs}:
      do Result<&2, &2, String, String>:
        init : String <- constructor(fs)
        body : String <- cases(fs)
        return object(init, body)

def main() -> IO(Unit):
  Tool.main(~contract, "Usage: compile.bend <contract.bend> <function>...")
