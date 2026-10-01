import Base
import ./Evm.bend as Evm

# The contract IR. Each constructor is one DSL call, so run(cmd) normalizes to
# the same term as the source contract; certificates check that with {==}.
#
# Bytes is a bytes parameter, which only an argument list can hold, and
# Length its length in bytes.
type Expr is Data:
  Lit{value: Nat}
  Var{level: Nat}
  Item{level: Nat, index: Nat}
  Bytes{level: Nat}
  Length{level: Nat}

type Cond is Data:
  Eq{left: Expr, right: Expr}
  Lt{left: Expr, right: Expr}
  Not{cond: Cond}

# A storage location: a plain slot, an entry of the mapping at base, or a
# slot of transient storage.
type Loc is Data:
  Plain{slot: Expr}
  Mapped{base: Loc, key: Expr}
  Temp{slot: Expr}

# Actions return a word; effects return Unit.
type Action is Data:
  SLoad{loc: Loc}
  Caller{}
  Add{left: Expr, right: Expr}
  Sub{left: Expr, right: Expr}
  Mul{left: Expr, right: Expr}
  Div{left: Expr, right: Expr}
  Mod{left: Expr, right: Expr}
  Math{op: Evm.Op, args: List<&2, Expr>}
  Select{cond: Cond, yes: Expr, no: Expr}
  Max{}
  Env{env: Evm.Env, args: List<&2, Expr>}
  Self{}
  Keccak{words: List<&2, Expr>}
  Typed{domain: Expr, message: Expr}
  Id{text: String}
  Recover{digest: Expr, v: Expr, r: Expr, s: Expr}
  View{target: Expr, signature: String, args: List<&2, Expr>}
  Call{target: Expr, signature: String, args: List<&2, Expr>}
  Hash{level: Nat}

type Effect is Data:
  SStore{loc: Loc, value: Expr}
  Log{event: String, topics: List<&2, Expr>, data: List<&2, Expr>}
  Require{cond: Cond}
  Ensure{cond: Cond, error: String, args: List<&2, Expr>}
  Pay{target: Expr, amount: Expr}
  Invoke{target: Expr, signature: String, args: List<&2, Expr>}

type Cmd is Data:
  Bind{word: Action, level: Nat, body: Cmd}
  Then{effect: Effect, body: Cmd}
  Return{value: Expr}
  Tail{word: Action}
  Finish{effect: Effect}
  Stop{}
  If{cond: Cond, yes: Cmd, no: Cmd}
  Give{signature: String, values: List<&2, Expr>}
  Fetch{target: Expr, signature: String, args: List<&2, Expr>, count: Nat, level: Nat, body: Cmd}

# What an entry point returns: a word, Unit, or several words. Give returns
# several words; its signature is the tuple def's, for the ABI, and the
# model keeps only the words. Fetch binds the first count words of a view
# call at level, and Item reads one.
type Output is Data:
  Returns{}
  Stops{}
  Gives{}

def value(out: Output) -> Data:
  match out:
    case Returns{}:
      Nat
    case Stops{}:
      Unit
    case Gives{}:
      Evm.Values

# A level holds a word, the words of a Fetch, or a bytes parameter. The
# printer names each word of a Fetch at level l as its own local, so an Item
# of a word level, or a Var of a Fetch level, names no local and solc
# rejects it.
type Binding is Data:
  Binding{level: Nat, value: Nat}
  Bindings{level: Nat, values: Evm.Values}
  Blob{level: Nat, value: Evm.Bytes}

def lookup(env: List<&2, Binding>, +level: Nat) -> Nat:
  match env:
    case Nil{}:
      0n
    case Binding{k, v} <> rest:
      Bool.pick(Nat, Nat.is_eq(k, level), v, lookup(rest, level))
    case Bindings{_, _} <> rest:
      lookup(rest, level)
    case Blob{_, _} <> rest:
      lookup(rest, level)

def values(env: List<&2, Binding>, +level: Nat) -> Evm.Values:
  match env:
    case Nil{}:
      Evm.Values{Nil{}}
    case Binding{_, _} <> rest:
      values(rest, level)
    case Bindings{k, v} <> rest:
      Bool.pick(Evm.Values, Nat.is_eq(k, level), v, values(rest, level))
    case Blob{_, _} <> rest:
      values(rest, level)

def blob(env: List<&2, Binding>, +level: Nat) -> Evm.Bytes:
  match env:
    case Nil{}:
      Evm.Bytes{0n, Nil{}}
    case Binding{_, _} <> rest:
      blob(rest, level)
    case Bindings{_, _} <> rest:
      blob(rest, level)
    case Blob{k, b} <> rest:
      Bool.pick(Evm.Bytes, Nat.is_eq(k, level), b, blob(rest, level))

def eval(expr: Expr, +env: List<&2, Binding>) -> Nat:
  match expr:
    case Lit{value}:
      value
    case Var{level}:
      lookup(env, level)
    case Item{level, index}:
      Evm.item(values(env, level), index)
    case Bytes{_}:
      0n
    case Length{level}:
      Evm.length(blob(env, level))

def evals(exprs: List<&2, Expr>, +env: List<&2, Binding>) -> List<&2, Nat>:
  match exprs:
    case Nil{}:
      Nil{}
    case e <> rest:
      eval(e, env) <> evals(rest, env)

def part(e: Expr, +env: List<&2, Binding>) -> Evm.Part:
  match e:
    case Bytes{level}:
      Evm.Dynamic{blob(env, level)}
    case +other:
      Evm.Word{eval(other, env)}

def parts(exprs: List<&2, Expr>, +env: List<&2, Binding>) -> List<&2, Evm.Part>:
  match exprs:
    case Nil{}:
      Nil{}
    case e <> rest:
      part(e, env) <> parts(rest, env)

# The ABI encoding of an argument list: of a log's data, an error's or a
# call's arguments, or a function's results.
def encode(exprs: List<&2, Expr>, +env: List<&2, Binding>) -> List<&2, Nat>:
  Evm.abi(parts(exprs, env))

def loc(l: Loc, +env: List<&2, Binding>) -> Evm.Key:
  match l:
    case Plain{slot}:
      Evm.Plain{eval(slot, env)}
    case Mapped{base, key}:
      Evm.Mapped{loc(base, env), eval(key, env)}
    case Temp{slot}:
      Evm.Transient{eval(slot, env)}

def cond(c: Cond, +env: List<&2, Binding>) -> Bool:
  match c:
    case Eq{left, right}:
      Nat.is_eq(eval(left, env), eval(right, env))
    case Lt{left, right}:
      Nat.is_lt(eval(left, env), eval(right, env))
    case Not{c}:
      Bool.not(cond(c, env))

# The name in a signature, the text before its "(". The IR keeps a log's,
# an error's or a call's signature for the printer, and the model keeps its
# name.
def name(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, rest}:
      Bool.pick(String, Char.is_eq(c, '('), SNil{}, SCon{c, name(rest)})

def word(w: Action, +env: List<&2, Binding>) -> Evm.Contract(Nat):
  match w:
    case SLoad{l}:
      Evm.read(loc(l, env))
    case Caller{}:
      Evm.caller()
    case Add{left, right}:
      Evm.add(eval(left, env), eval(right, env))
    case Sub{left, right}:
      Evm.sub(eval(left, env), eval(right, env))
    case Mul{left, right}:
      Evm.mul(eval(left, env), eval(right, env))
    case Div{left, right}:
      Evm.div(eval(left, env), eval(right, env))
    case Mod{left, right}:
      Evm.mod(eval(left, env), eval(right, env))
    case Math{op, args}:
      Evm.math(op, evals(args, env))
    case Select{c, yes, no}:
      Evm.select(cond(c, env), eval(yes, env), eval(no, env))
    case Max{}:
      Evm.max()
    case Env{e, args}:
      Evm.env(e, evals(args, env))
    case Self{}:
      Evm.self()
    case Keccak{words}:
      Evm.keccak(evals(words, env))
    case Typed{domain, message}:
      Evm.typed(eval(domain, env), eval(message, env))
    case Id{text}:
      Evm.id(text)
    case Recover{digest, v, r, s}:
      Evm.recover(eval(digest, env), eval(v, env), eval(r, env), eval(s, env))
    case View{target, signature, args}:
      Evm.view(Evm.Call{eval(target, env), name(signature), encode(args, env)})
    case Call{target, signature, args}:
      Evm.call(Evm.Call{eval(target, env), name(signature), encode(args, env)})
    case Hash{level}:
      Evm.keccak.bytes(blob(env, level))

def effect(e: Effect, +env: List<&2, Binding>) -> Evm.Contract(Unit):
  match e:
    case SStore{l, value}:
      Evm.write(loc(l, env), eval(value, env))
    case Log{event, topics, data}:
      Evm.log(name(event), evals(topics, env), encode(data, env))
    case Require{c}:
      Evm.require(cond(c, env))
    case Ensure{c, error, args}:
      Evm.ensure(cond(c, env), Evm.Error{name(error), encode(args, env)})
    case Pay{target, amount}:
      Evm.pay(eval(target, env), eval(amount, env))
    case Invoke{target, signature, args}:
      Evm.invoke(Evm.Call{eval(target, env), name(signature), encode(args, env)})

def abort(-A: Data) -> Evm.Contract(A):
  R => k => s => Evm.Revert{}

# A tail whose kind differs from the entry's output is ill-formed and reverts.
def run(cmd: Cmd, +out: Output, +env: List<&2, Binding>) -> Evm.Contract(value(out)):
  match cmd out:
    case Bind{w, level, body} o:
      Evm.Contract.bind(Nat, value(o), word(w, env), x => run(body, o, Binding{level, x} <> env))
    case Then{e, body} o:
      Evm.Contract.bind(Unit, value(o), effect(e, env), _ => run(body, o, env))
    case Return{v} Returns{}:
      Evm.Contract.pure(Nat, eval(v, env))
    case Tail{w} Returns{}:
      word(w, env)
    case Finish{e} Stops{}:
      effect(e, env)
    case Stop{} Stops{}:
      Evm.Contract.pure(Unit, Unit{})
    case If{c, yes, no} o:
      Evm.branch(value(o), cond(c, env), run(yes, o, env), run(no, o, env))
    case Give{_, vs} Gives{}:
      Evm.Contract.pure(Evm.Values, Evm.Values{encode(vs, env)})
    case Fetch{target, signature, args, count, level, body} o:
      Evm.Contract.bind(Evm.Values, value(o), Evm.views(Evm.Call{eval(target, env), name(signature), encode(args, env)}, count),
        v => run(body, o, Bindings{level, v} <> env))
    case _ o:
      abort(value(o))

# Scope checks: an unbound Var would read as 0 in lookup and could hide a
# wrong IR behind a literal 0 in the source.
def has(levels: List<&2, Nat>, +level: Nat) -> Bool:
  match levels:
    case Nil{}:
      False{}
    case k <> rest:
      Bool.or(Nat.is_eq(k, level), has(rest, level))

def closed.expr(e: Expr, +scope: List<&2, Nat>) -> Bool:
  match e:
    case Lit{_}:
      True{}
    case Var{level}:
      has(scope, level)
    case Item{level, _}:
      has(scope, level)
    case Bytes{_}:
      False{}
    case Length{level}:
      has(scope, level)

def closed.two(left: Expr, right: Expr, +scope: List<&2, Nat>) -> Bool:
  Bool.and(closed.expr(left, scope), closed.expr(right, scope))

def closed.list(exprs: List<&2, Expr>, +scope: List<&2, Nat>) -> Bool:
  match exprs:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(closed.expr(e, scope), closed.list(rest, scope))

# An argument list may also hold bytes.
def closed.part(e: Expr, +scope: List<&2, Nat>) -> Bool:
  match e:
    case Bytes{level}:
      has(scope, level)
    case +other:
      closed.expr(other, scope)

def closed.parts(exprs: List<&2, Expr>, +scope: List<&2, Nat>) -> Bool:
  match exprs:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(closed.part(e, scope), closed.parts(rest, scope))

def closed.cond(c: Cond, +scope: List<&2, Nat>) -> Bool:
  match c:
    case Eq{left, right}:
      closed.two(left, right, scope)
    case Lt{left, right}:
      closed.two(left, right, scope)
    case Not{c}:
      closed.cond(c, scope)

def closed.loc(l: Loc, +scope: List<&2, Nat>) -> Bool:
  match l:
    case Plain{slot}:
      closed.expr(slot, scope)
    case Mapped{base, key}:
      Bool.and(closed.loc(base, scope), closed.expr(key, scope))
    case Temp{slot}:
      closed.expr(slot, scope)

def closed.word(w: Action, +scope: List<&2, Nat>) -> Bool:
  match w:
    case SLoad{l}:
      closed.loc(l, scope)
    case Caller{}:
      True{}
    case Add{left, right}:
      closed.two(left, right, scope)
    case Sub{left, right}:
      closed.two(left, right, scope)
    case Mul{left, right}:
      closed.two(left, right, scope)
    case Div{left, right}:
      closed.two(left, right, scope)
    case Mod{left, right}:
      closed.two(left, right, scope)
    case Math{_, args}:
      closed.list(args, scope)
    case Select{c, yes, no}:
      Bool.and(closed.cond(c, scope), closed.two(yes, no, scope))
    case Max{}:
      True{}
    case Env{_, args}:
      closed.list(args, scope)
    case Self{}:
      True{}
    case Keccak{words}:
      closed.list(words, scope)
    case Typed{domain, message}:
      closed.two(domain, message, scope)
    case Id{_}:
      True{}
    case Recover{digest, v, r, s}:
      Bool.and(closed.two(digest, v, scope), closed.two(r, s, scope))
    case View{target, _, args}:
      Bool.and(closed.expr(target, scope), closed.parts(args, scope))
    case Call{target, _, args}:
      Bool.and(closed.expr(target, scope), closed.parts(args, scope))
    case Hash{level}:
      has(scope, level)

def closed.effect(e: Effect, +scope: List<&2, Nat>) -> Bool:
  match e:
    case SStore{l, value}:
      Bool.and(closed.loc(l, scope), closed.expr(value, scope))
    case Log{_, topics, data}:
      Bool.and(closed.list(topics, scope), closed.parts(data, scope))
    case Require{c}:
      closed.cond(c, scope)
    case Ensure{c, _, args}:
      Bool.and(closed.cond(c, scope), closed.parts(args, scope))
    case Pay{target, amount}:
      closed.two(target, amount, scope)
    case Invoke{target, _, args}:
      Bool.and(closed.expr(target, scope), closed.parts(args, scope))

def closed(cmd: Cmd, +scope: List<&2, Nat>) -> Bool:
  match cmd:
    case Bind{w, level, body}:
      Bool.and(closed.word(w, scope), closed(body, level <> scope))
    case Then{e, body}:
      Bool.and(closed.effect(e, scope), closed(body, scope))
    case Return{v}:
      closed.expr(v, scope)
    case Tail{w}:
      closed.word(w, scope)
    case Finish{e}:
      closed.effect(e, scope)
    case Stop{}:
      True{}
    case If{c, yes, no}:
      Bool.and(closed.cond(c, scope), Bool.and(closed(yes, scope), closed(no, scope)))
    case Give{_, vs}:
      closed.parts(vs, scope)
    case Fetch{target, _, args, _, level, body}:
      Bool.and(Bool.and(closed.expr(target, scope), closed.parts(args, scope)), closed(body, level <> scope))

def levels(env: List<&2, Binding>) -> List<&2, Nat>:
  match env:
    case Nil{}:
      Nil{}
    case Binding{level, _} <> rest:
      level <> levels(rest)
    case Bindings{level, _} <> rest:
      level <> levels(rest)
    case Blob{level, _} <> rest:
      level <> levels(rest)

# An entry point: reverts unless every variable is bound, then runs.
def call(+cmd: Cmd, +out: Output, +env: List<&2, Binding>) -> Evm.Contract(value(out)):
  Bool.pick(Evm.Contract(value(out)), closed(cmd, levels(env)), run(cmd, out, env), abort(value(out)))
