import Base
import ./Evm.bend as Evm
import ./ir.bend as IR
import ./read.bend as Read
import ./yul.bend as Yul
import ./keccak.bend as Keccak
import ./tool.bend as Tool

# Prints a Yul object for the named entries, with an ABI dispatcher. The
# dispatcher range-checks address, uint8 and bool parameters; results go out
# as they are. A bytes or string parameter stays in the calldata: its local
# is the position of its length word there. An entry named init is the
# constructor.
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
    case IR.Item{level, index}:
      var(level) ++ "_" ++ nat(index)
    case IR.Bytes{level}:
      var(level)
    case IR.Length{level}:
      "calldataload(" ++ var(level) ++ ")"

def call(name: String, args: List<&2, String>) -> String:
  name ++ "(" ++ String.join(args, ", ") ++ ")"

# A mapping entry lives at keccak256(key . base), as in Solidity.
def loc(l: IR.Loc) -> String:
  match l:
    case IR.Plain{slot}:
      atom(slot)
    case IR.Mapped{base, key}:
      call("mapped", [loc(base), atom(key)])
    case IR.Temp{slot}:
      atom(slot)

# A transient location is read with tload and written with tstore.
def transient(l: IR.Loc) -> Bool:
  match l:
    case IR.Plain{_}:
      False{}
    case IR.Mapped{base, _}:
      transient(base)
    case IR.Temp{_}:
      True{}

def load(+l: IR.Loc) -> String:
  call(Bool.pick(String, transient(l), "tload", "sload"), [loc(l)])

def atoms(exprs: List<&2, IR.Expr>) -> List<&2, String>:
  match exprs:
    case Nil{}:
      Nil{}
    case e <> rest:
      atom(e) <> atoms(rest)

def yul(i: Evm.Info) -> String:
  match i:
    case Evm.Info{_, y, _, _}:
      y

def exp(e: Yul.Exp) -> String:
  match e:
    case Yul.Atom{value}:
      atom(value)
    case Yul.SLoad{+l}:
      load(l)
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
    case Yul.Op{op, args}:
      call(yul(Evm.info(op)), atoms(args))
    case Yul.Div{left, right}:
      a b = exp(left) exp(right)
      call("div", [a, b])
    case Yul.And{left, right}:
      a b = exp(left) exp(right)
      call("and", [a, b])
    case Yul.Hash{level}:
      call("keccak256", ["0", atom(IR.Length{level})])

def sense(e: Evm.Env, args: List<&2, IR.Expr>) -> String:
  call(yul(Evm.info.of(Evm.sensor(e))), atoms(args))

def revert() -> String:
  "revert(0, 0)"

# Word i goes to memory at offset + 32 * i: log data from 0, and error and
# call arguments from 4, after the selector.
def stores(+pad: String, data: List<&2, IR.Expr>, +offset: Nat) -> String:
  match data:
    case Nil{}:
      ""
    case d <> rest:
      pad ++ call("mstore", [nat(offset), atom(d)]) ++ "\n" ++ stores(pad, rest, Nat.add(32n, offset))

# keccak256 reads from memory at 0, so the words or the bytes go there first.
def prelude(+pad: String, value: Yul.Exp) -> String:
  match value:
    case Yul.Keccak{words}:
      stores(pad, words, 0n)
    case Yul.Hash{+level}:
      pad ++ call("calldatacopy", ["0", call("add", [var(level), "32"]), atom(IR.Length{level})]) ++ "\n"
    case _:
      ""

def has.bytes(args: List<&2, IR.Expr>) -> Bool:
  match args:
    case Nil{}:
      False{}
    case IR.Bytes{_} <> _:
      True{}
    case _ <> rest:
      has.bytes(rest)

# The heads of an encoding with bytes, from offset on: each bytes value's
# head is its offset from base, and put copies it to end.
def heads(+pad: String, args: List<&2, IR.Expr>, +base: Nat, +offset: Nat) -> String:
  match args:
    case Nil{}:
      ""
    case IR.Bytes{level} <> rest:
      pad ++ call("mstore", [nat(offset), Bool.pick(String, Nat.is_eq(base, 0n), "end", call("sub", ["end", nat(base)]))]) ++ "\n"
        ++ pad ++ "end := " ++ call("put", ["end", var(level)]) ++ "\n" ++ heads(pad, rest, base, Nat.add(32n, offset))
    case e <> rest:
      pad ++ call("mstore", [nat(offset), atom(e)]) ++ "\n" ++ heads(pad, rest, base, Nat.add(32n, offset))

# The ABI encoding of args in memory from base, then use(pad, end), the
# statement that reads it up to end. With bytes, the end is known only when
# the code runs, so the encoding is a block with a local end.
def encoded(+pad: String, +args: List<&2, IR.Expr>, +base: Nat, use: String -> String -> String) -> String:
  +size = Nat.add(base, Nat.mul(32n, List.length(&2, IR.Expr, args)))
  +inner = pad ++ "  "
  +block = has.bytes(args)
  Bool.pick(String, block, pad ++ "{\n" ++ inner ++ "let end := " ++ nat(size) ++ "\n" ++ heads(inner, args, base, base),
    stores(pad, args, base))
    ++ use(Bool.pick(String, block, inner, pad), Bool.pick(String, block, "end", nat(size)))
    ++ Bool.pick(String, block, pad ++ "}\n", "")

# A call to another contract, with staticcall for a view and with call and
# no value otherwise: the selector and argument words go to memory at 0, and
# the first words returned come back to 0. When the call fails, the
# contract reverts with the callee's revert data, as Solidity does; when it
# returns fewer words, with no data. A callback into this contract runs in a
# new frame with its own memory, so it cannot change these words.
def made(+pad: String, +writes: Bool, +target: IR.Expr, +out: String, +size: String) -> String:
  +sent = Bool.pick(String, writes, call("call", ["gas()", atom(target), "0", "0", size, "0", out]),
    call("staticcall", ["gas()", atom(target), "0", size, "0", out]))
  pad ++ "if iszero(" ++ sent ++ ") {\n"
    ++ pad ++ "  returndatacopy(0, 0, returndatasize())\n"
    ++ pad ++ "  revert(0, returndatasize())\n"
    ++ pad ++ "}\n"

def external(+pad: String, +writes: Bool, +target: IR.Expr, +signature: String, +args: List<&2, IR.Expr>, +words: Nat) ->
  String:
  +out = nat(Nat.mul(32n, words))
  pad ++ call("mstore", ["0", call("shl", ["224", Keccak.hex(Keccak.selector(signature))])]) ++ "\n"
    ++ encoded(pad, args, 4n, p => size => made(p, writes, target, out, size))
    ++ Bool.pick(String, Nat.is_eq(words, 0n), "", pad ++ "if lt(returndatasize(), " ++ out ++ ") { " ++ revert() ++ " }\n")

# The locals of a Fetch at level: one for each word.
def fetched(n: Nat, +pad: String, +level: Nat, +i: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+m:
      pad ++ "let " ++ atom(IR.Item{level, i}) ++ " := " ++ call("mload", [nat(Nat.mul(32n, i))]) ++ "\n"
        ++ fetched(m, pad, level, Nat.add(i, 1n))

# halt is the text for a final stop: stop() in the runtime code, nothing in
# the deploy code.
def stmt(+pad: String, +halt: String, s: Yul.Stmt) -> String:
  match s:
    case Yul.Let{level, +value, body}:
      prelude(pad, value) ++ pad ++ "let " ++ var(level) ++ " := " ++ exp(value) ++ "\n" ++ stmt(pad, halt, body)
    case Yul.SStore{+l, value, body}:
      pad ++ call(Bool.pick(String, transient(l), "tstore", "sstore"), [loc(l), exp(value)]) ++ "\n" ++ stmt(pad, halt, body)
    case Yul.Log{+event, +topics, +data, body}:
      +n = Nat.add(1n, List.length(&2, IR.Expr, topics))
      encoded(pad, data, 0n, p => size => p ++ call("log" ++ nat(n), "0" <> size <> Keccak.digest(event) <> atoms(topics)) ++ "\n")
        ++ stmt(pad, halt, body)
    case Yul.Check{cond, body}:
      pad ++ "if " ++ exp(cond) ++ " { " ++ revert() ++ " }\n" ++ stmt(pad, halt, body)
    case Yul.Guard{cond, +error, +args, body}:
      +inner = pad ++ "  "
      pad ++ "if " ++ exp(cond) ++ " {\n" ++ inner ++ call("mstore", ["0", call("shl", ["224", Keccak.hex(Keccak.selector(error))])])
        ++ "\n" ++ encoded(inner, args, 4n, p => size => p ++ call("revert", ["0", size]) ++ "\n") ++ pad ++ "}\n"
        ++ stmt(pad, halt, body)
    case Yul.View{level, target, +signature, +args, body}:
      external(pad, False{}, target, signature, args, 1n) ++ pad ++ "let " ++ var(level) ++ " := mload(0)\n" ++ stmt(pad, halt, body)
    case Yul.Call{level, target, +signature, +args, body}:
      external(pad, True{}, target, signature, args, 1n) ++ pad ++ "let " ++ var(level) ++ " := mload(0)\n" ++ stmt(pad, halt, body)
    case Yul.Reply{target, +signature, +args}:
      external(pad, True{}, target, signature, args, 1n) ++ pad ++ "return(0, 32)\n"
    case Yul.Answer{target, +signature, +args}:
      external(pad, False{}, target, signature, args, 1n) ++ pad ++ "return(0, 32)\n"
    case Yul.Fetch{+level, target, +signature, +args, +count, body}:
      external(pad, False{}, target, signature, args, count) ++ fetched(count, pad, level, 0n) ++ stmt(pad, halt, body)
    case Yul.Results{+values}:
      encoded(pad, values, 0n, p => size => p ++ call("return", ["0", size]) ++ "\n")
    case Yul.Pay{target, amount, body}:
      pad ++ "if iszero(" ++ call("call", ["gas()", atom(target), atom(amount), "0", "0", "0", "0"]) ++ ") { " ++ revert() ++ " }\n"
        ++ stmt(pad, halt, body)
    case Yul.Invoke{+target, +signature, +args, body}:
      pad ++ "if iszero(extcodesize(" ++ atom(target) ++ ")) { " ++ revert() ++ " }\n"
        ++ external(pad, True{}, target, signature, args, 0n) ++ stmt(pad, halt, body)
    case Yul.Sense{level, e, args, body}:
      pad ++ "let " ++ var(level) ++ " := " ++ sense(e, args) ++ "\n" ++ stmt(pad, halt, body)
    case Yul.Sensed{e, args}:
      pad ++ "mstore(0, " ++ sense(e, args) ++ ")\n" ++ pad ++ "return(0, 32)\n"
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
# A bytes parameter, only in the runtime, is the position of its length
# word, which dynamic checks.
def parameters(+pad: String, +load: String, +base: Nat, types: List<&2, String>, +level: Nat) -> String:
  match types:
    case Nil{}:
      ""
    case +typ <> rest:
      +offset = Nat.add(base, Nat.mul(32n, level))
      Bool.pick(String, Read.dynamic(typ), pad ++ "let " ++ var(level) ++ " := dynamic(" ++ nat(offset) ++ ")\n",
        pad ++ "let " ++ var(level) ++ " := " ++ load ++ "(" ++ nat(offset) ++ ")\n" ++ range(pad, typ, level))
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
def literal(e: IR.Expr) -> Bool:
  match e:
    case IR.Lit{_}:
      True{}
    case _:
      False{}

def fixed.loc(l: IR.Loc) -> Bool:
  match l:
    case IR.Plain{slot}:
      literal(slot)
    case IR.Mapped{base, _}:
      fixed.loc(base)
    case IR.Temp{slot}:
      literal(slot)

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
    case IR.Fetch{_, _, _, _, _, body}:
      fixed(body)
    case _:
      True{}

# An entry compiles only if its variables are bound and its slots are fixed.
def valid(+name: String, +body: IR.Cmd, +levels: List<&2, Nat>) -> Result<&2, &2, String, IR.Cmd>:
  Bool.pick(Result<&2, &2, String, IR.Cmd>, Bool.and(IR.closed(body, levels), fixed(body)), Done{body},
    Fail{name ++ ": the IR has an unbound variable or a storage slot that is not a literal"})

# The check that a call sent no ether.
def no.value(+pad: String) -> String:
  pad ++ "if callvalue() { " ++ revert() ++ " }\n"

# The dispatcher case of a contract function: its selector, the check for
# ether if any, the calldata size check, its parameters, then its lowered
# body.
def dispatch.text(+signature: String, +check: String, +types: List<&2, String>, body: Yul.Stmt) -> String:
  +pad = indent()
  +size = Nat.add(4n, Nat.mul(32n, List.length(&2, String, types)))
  "      case " ++ Keccak.hex(Keccak.selector(signature)) ++ " {\n" ++ check
    ++ pad ++ "if lt(calldatasize(), " ++ nat(size) ++ ") { " ++ revert() ++ " }\n"
    ++ parameters(pad, "calldataload", 4n, types, 0n) ++ stmt(pad, pad ++ "stop()\n", body) ++ "      }\n"

def dispatch.valid(+signature: String, +check: String, +types: List<&2, String>, +levels: List<&2, Nat>, +body: IR.Cmd) ->
  Result<&2, &2, String, String>:
  do Result<&2, &2, String, String>:
    +checked : IR.Cmd <- valid(signature, body, levels)
    return dispatch.text(signature, check, types, Yul.lower(checked, Read.output(checked)))

def dispatch(+name: String, +check: String, inputs: List<&2, Read.Input>, entry: Read.Entry) -> Result<&2, &2, String, String>:
  match entry:
    case Read.Entry{+levels, +body}:
      +ts = types(inputs)
      +signature = name ++ "(" ++ String.join(ts, ",") ++ ")"
      Bool.pick(Result<&2, &2, String, String>, Keccak.fits(signature), dispatch.valid(signature, check, ts, levels, body),
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
def constant.text(+name: String, +check: String, +value: String) -> String:
  +pad = indent()
  +size = String.length(value)
  "      case " ++ Keccak.hex(Keccak.selector(name ++ "()")) ++ " {\n" ++ check
    ++ pad ++ "mstore(0, 32)\n" ++ pad ++ "mstore(32, " ++ nat(size) ++ ")\n"
    ++ mstores(size, pad, value, 64n)
    ++ pad ++ "return(0, " ++ nat(Nat.add(64n, Nat.mul(32n, Nat.div(Nat.add(size, 31n), 32n)))) ++ ")\n      }\n"

def constant.ascii(+name: String, +check: String, +value: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, Keccak.ascii(value), Done{constant.text(name, check, value)},
    Fail{name ++ ": a constant string must be ASCII"})

def constant(+name: String, +check: String, +value: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, Keccak.fits(name ++ "()"), constant.ascii(name, check, value),
    Fail{name ++ "(): signatures over 135 bytes are not supported"})

# When some entry is payable, each other one checks for ether itself;
# otherwise the dispatcher checks once, before the switch.
def case.text(+each: Bool, f: Read.Function) -> Result<&2, &2, String, String>:
  match f:
    case Read.Constant{+name, +value}:
      constant(name, Bool.pick(String, each, no.value(indent()), ""), value)
    case Read.Contract{+name, inputs, _, payable, entry}:
      dispatch(name, Bool.pick(String, Bool.and(each, Bool.not(payable)), no.value(indent()), ""), inputs, entry)

def is_named(+n: String, f: Read.Function) -> Bool:
  match f:
    case Read.Contract{name, _, _, _, _}:
      String.eq(name, n)
    case Read.Constant{_, _}:
      False{}

def is_init(f: Read.Function) -> Bool:
  is_named("init", f)

# init runs in the deploy code, and receive when the calldata is empty.
def special(+f: Read.Function) -> Bool:
  Bool.or(is_init(f), is_named("receive", f))

def is_payable(f: Read.Function) -> Bool:
  match f:
    case Read.Contract{_, _, _, payable, _}:
      payable
    case Read.Constant{_, _}:
      False{}

def any_payable(fs: List<&2, Read.Function>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case +f <> rest:
      Bool.or(Bool.and(is_payable(f), Bool.not(is_init(f))), any_payable(rest))

def cases(+each: Bool, fs: List<&2, Read.Function>) -> Result<&2, &2, String, String>:
  match fs:
    case Nil{}:
      Done{""}
    case +f <> rest:
      do Result<&2, &2, String, String>:
        head : String <- Bool.pick(Result<&2, &2, String, String>, special(f), Done{""}, case.text(each, f))
        tail : String <- cases(each, rest)
        return head ++ tail

# Yul functions that lowered code calls. Each code block defines its own.
# dynamic gives the position of a bytes parameter's length word from the
# position of its head. It reverts unless the offset is a multiple of 32,
# as the model of callbacks decodes words, the bytes end in the calldata,
# and the padding after them is zero. put copies bytes from the calldata to
# memory, as the ABI encodes them, zero-padded, and gives the end.
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
    ++ pad ++ "function dynamic(head) -> at {\n"
    ++ pad ++ "  let offset := calldataload(head)\n"
    ++ pad ++ "  if or(and(offset, 31), gt(offset, 0xffffffff)) { revert(0, 0) }\n"
    ++ pad ++ "  at := add(4, offset)\n"
    ++ pad ++ "  if gt(add(at, 32), calldatasize()) { revert(0, 0) }\n"
    ++ pad ++ "  let n := calldataload(at)\n"
    ++ pad ++ "  if gt(n, sub(calldatasize(), add(at, 32))) { revert(0, 0) }\n"
    ++ pad ++ "  let k := and(n, 31)\n"
    ++ pad ++ "  if k { if shl(shl(3, k), calldataload(add(add(at, 32), sub(n, k)))) { revert(0, 0) } }\n"
    ++ pad ++ "}\n"
    ++ pad ++ "function put(at, from) -> next {\n"
    ++ pad ++ "  let n := calldataload(from)\n"
    ++ pad ++ "  mstore(at, n)\n"
    ++ pad ++ "  mstore(add(add(at, 32), and(n, not(31))), 0)\n"
    ++ pad ++ "  calldatacopy(add(at, 32), add(from, 32), n)\n"
    ++ pad ++ "  next := add(add(at, 32), and(add(n, 31), not(31)))\n"
    ++ pad ++ "}\n"

# deploy and runtime are the checks for ether, if any, and receive the code
# for empty calldata, if any.
def object(+deploy: String, init: String, +runtime: String, receive: String, body: String) -> String:
  "object \"Contract\" {\n"
    ++ "  code {\n"
    ++ helpers("    ")
    ++ deploy
    ++ init
    ++ "    datacopy(0, dataoffset(\"runtime\"), datasize(\"runtime\"))\n"
    ++ "    return(0, datasize(\"runtime\"))\n"
    ++ "  }\n"
    ++ "  object \"runtime\" {\n"
    ++ "    code {\n"
    ++ helpers("      ")
    ++ runtime
    ++ receive
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

def any.dynamic(ts: List<&2, String>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case +t <> rest:
      Bool.or(Read.dynamic(t), any.dynamic(rest))

def init.stops(out: IR.Output, inputs: List<&2, Read.Input>, +levels: List<&2, Nat>, +body: IR.Cmd) ->
  Result<&2, &2, String, String>:
  match out:
    case IR.Stops{}:
      +ts = types(inputs)
      Bool.pick(Result<&2, &2, String, String>, any.dynamic(ts), Fail{"init takes no bytes or string parameters"},
        do Result<&2, &2, String, String>:
          checked : IR.Cmd <- valid("init", body, levels)
          return arguments(ts) ++ stmt("    ", "", Yul.lower(checked, IR.Stops{})))
    case _:
      Fail{"init must return Unit"}

def constructor.of(f: Read.Function) -> Result<&2, &2, String, String>:
  match f:
    case Read.Contract{_, inputs, _, _, Read.Entry{+levels, +body}}:
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

# An entry named receive runs when the calldata is empty, as Solidity's
# receive(). It must be payable, take no parameters and return Unit.
def receive.stops(out: IR.Output, +levels: List<&2, Nat>, +body: IR.Cmd) -> Result<&2, &2, String, String>:
  match out:
    case IR.Stops{}:
      do Result<&2, &2, String, String>:
        checked : IR.Cmd <- valid("receive", body, levels)
        return "      if iszero(calldatasize()) {\n" ++ stmt(indent(), indent() ++ "stop()\n", Yul.lower(checked, IR.Stops{}))
          ++ "      }\n"
    case _:
      Fail{"receive must return Unit"}

def receive.of(f: Read.Function) -> Result<&2, &2, String, String>:
  match f:
    case Read.Contract{_, inputs, _, payable, Read.Entry{+levels, +body}}:
      Bool.pick(Result<&2, &2, String, String>, Bool.and(payable, Nat.is_eq(List.length(&2, Read.Input, inputs), 0n)),
        receive.stops(Read.output(body), levels, body), Fail{"receive must be payable and take no parameters"})
    case Read.Constant{_, _}:
      Fail{"receive must be payable and take no parameters"}

def receive(fs: List<&2, Read.Function>) -> Result<&2, &2, String, String>:
  match fs:
    case Nil{}:
      Done{""}
    case +f <> rest:
      Bool.pick(Result<&2, &2, String, String>, is_named("receive", f), receive.of(f), receive(rest))

def init.payable(fs: List<&2, Read.Function>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case +f <> rest:
      Bool.or(Bool.and(is_init(f), is_payable(f)), init.payable(rest))

def contract(file: String, s: Tool.Setup) -> Result<&2, &2, String, String>:
  match s:
    case Tool.Setup{_, +fs, _}:
      +each = any_payable(fs)
      do Result<&2, &2, String, String>:
        init : String <- constructor(fs)
        got : String <- receive(fs)
        body : String <- cases(each, fs)
        return object(Bool.pick(String, init.payable(fs), "", no.value("    ")), init,
          Bool.pick(String, each, "", no.value("      ")), got, body)

def main() -> IO(Unit):
  Tool.main(~contract, "Usage: compile.bend <contract.bend> <function>...")
