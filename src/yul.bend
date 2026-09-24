import Base
import ./Evm.bend as Evm
import ./ir.bend as IR

# The Yul fragment that the IR needs, not all of Yul. Expressions only read
# state; statements change it. An atom is a literal or a local, as in the IR,
# and a local is named by its IR level.
type Exp is Data:
  Atom{value: IR.Expr}
  SLoad{key: Exp}
  Caller{}
  Add{left: Exp, right: Exp}
  Sub{left: Exp, right: Exp}
  Not{value: Exp}
  Eq{left: Exp, right: Exp}
  Lt{left: Exp, right: Exp}
  Gt{left: Exp, right: Exp}
  IsZero{value: Exp}

# Each statement holds the rest of its block, so a block is one Stmt.
type Stmt is Data:
  Let{level: Nat, value: Exp, body: Stmt}
  SStore{key: Exp, value: Exp, body: Stmt}
  Check{cond: Exp, body: Stmt}
  Result{value: Exp}
  Stop{}
  Revert{}

def storage(s: Evm.State, +key: Nat) -> Nat:
  match s:
    case Evm.State{storage, _, _}:
      Evm.lookup(storage, key)

def caller(s: Evm.State) -> Nat:
  match s:
    case Evm.State{_, caller, _}:
      caller

def limit(s: Evm.State) -> Nat:
  match s:
    case Evm.State{_, _, limit}:
      limit

# Yul comparisons return the word 1 or 0.
def bit(c: Bool) -> Nat:
  Bool.pick(Nat, c, 1n, 0n)

# EVM arithmetic modulo the limit. On words below the limit these are the
# EVM's operations. Above it the EVM has no words, so the model picks results
# that make the overflow check revert, and the proof needs no range invariant.
def add(+x: Nat, +y: Nat, +l: Nat) -> Nat:
  +s = Nat.add(x, y)
  Bool.pick(Nat, Nat.is_lt(s, l), s, Nat.sub(s, l))

def sub(+x: Nat, +y: Nat, +l: Nat) -> Nat:
  Bool.pick(Nat, Bool.and(Nat.is_lt(x, l), Nat.is_lt(y, l)),
    Bool.pick(Nat, Nat.is_lt(x, y), Nat.sub(l, Nat.sub(y, x)), Nat.sub(x, y)), l)

def not(+x: Nat, +l: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(x, l), Nat.sub(Nat.sub(l, 1n), x), l)

def gt(+x: Nat, +y: Nat, +l: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(y, l), bit(Nat.is_lt(y, x)), 1n)

def eval(e: Exp, +env: List<&2, IR.Binding>, +s: Evm.State) -> Nat:
  match e:
    case Atom{value}:
      IR.eval(value, env)
    case SLoad{key}:
      storage(s, eval(key, env, s))
    case Caller{}:
      caller(s)
    case Add{left, right}:
      a b = eval(left, env, s) eval(right, env, s)
      add(a, b, limit(s))
    case Sub{left, right}:
      a b = eval(left, env, s) eval(right, env, s)
      sub(a, b, limit(s))
    case Not{value}:
      not(eval(value, env, s), limit(s))
    case Eq{left, right}:
      a b = eval(left, env, s) eval(right, env, s)
      bit(Nat.is_eq(a, b))
    case Lt{left, right}:
      a b = eval(left, env, s) eval(right, env, s)
      bit(Nat.is_lt(a, b))
    case Gt{left, right}:
      a b = eval(left, env, s) eval(right, env, s)
      gt(a, b, limit(s))
    case IsZero{value}:
      bit(Nat.is_eq(eval(value, env, s), 0n))

# `if cond { revert(0, 0) }` reverts when cond is not zero.
def exec(stmt: Stmt, +out: IR.Output, +env: List<&2, IR.Binding>) -> Evm.Contract(IR.value(out)):
  match stmt out:
    case Let{level, value, body} o:
      +s => exec(body, o, IR.Binding{level, eval(value, env, s)} <> env, s)
    case SStore{key, value, body} o:
      +s => Evm.Contract.next(Unit, IR.value(o), Evm.sstore.go(eval(key, env, s), eval(value, env, s), s),
        _ => exec(body, o, env))
    case Check{cond, body} o:
      +s => Evm.Contract.next(Unit, IR.value(o), Evm.require.go(Nat.is_eq(eval(cond, env, s), 0n), s),
        _ => exec(body, o, env))
    case Result{value} IR.Returns{}:
      +s => Evm.Ok{eval(value, env, s), s}
    case Stop{} IR.Stops{}:
      s => Evm.Ok{Unit{}, s}
    case _ o:
      IR.abort(IR.value(o))

# The condition under which a Require reverts.
def lower.cond(c: IR.Cond) -> Exp:
  match c:
    case IR.Eq{left, right}:
      IsZero{Eq{Atom{left}, Atom{right}}}
    case IR.Lt{left, right}:
      IsZero{Lt{Atom{left}, Atom{right}}}

# Checked add reverts when b > not(0) - a, that is when a + b overflows.
def overflow(+left: IR.Expr, +right: IR.Expr) -> Exp:
  Gt{Atom{right}, Sub{Not{Atom{IR.Lit{0n}}}, Atom{left}}}

# The entry's output is known, so a tail of the wrong kind lowers to a revert.
def lower(cmd: IR.Cmd, +out: IR.Output) -> Stmt:
  match cmd out:
    case IR.Bind{IR.SLoad{key}, level, body} o:
      Let{level, SLoad{Atom{key}}, lower(body, o)}
    case IR.Bind{IR.Caller{}, level, body} o:
      Let{level, Caller{}, lower(body, o)}
    case IR.Bind{IR.Add{+left, +right}, level, body} o:
      Check{overflow(left, right), Let{level, Add{Atom{left}, Atom{right}}, lower(body, o)}}
    case IR.Then{IR.SStore{key, value}, body} o:
      SStore{Atom{key}, Atom{value}, lower(body, o)}
    case IR.Then{IR.Require{c}, body} o:
      Check{lower.cond(c), lower(body, o)}
    case IR.Return{value} IR.Returns{}:
      Result{Atom{value}}
    case IR.Tail{IR.SLoad{key}} IR.Returns{}:
      Result{SLoad{Atom{key}}}
    case IR.Tail{IR.Caller{}} IR.Returns{}:
      Result{Caller{}}
    case IR.Tail{IR.Add{+left, +right}} IR.Returns{}:
      Check{overflow(left, right), Result{Add{Atom{left}, Atom{right}}}}
    case IR.Finish{IR.SStore{key, value}} IR.Stops{}:
      SStore{Atom{key}, Atom{value}, Stop{}}
    case IR.Finish{IR.Require{c}} IR.Stops{}:
      Check{lower.cond(c), Stop{}}
    case IR.Stop{} IR.Stops{}:
      Stop{}
    case _ _:
      Revert{}
