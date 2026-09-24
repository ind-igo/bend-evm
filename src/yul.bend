import Base
import ./Evm.bend as Evm
import ./ir.bend as IR

# The Yul fragment that the IR needs, not all of Yul. Expressions only read
# state; statements change it. An atom is a literal or a local, as in the IR,
# and a local is named by its IR level. A storage location is an IR.Loc: the
# printer turns a mapping entry into keccak256(key . slot).
type Exp is Data:
  Atom{value: IR.Expr}
  SLoad{loc: IR.Loc}
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
  SStore{loc: IR.Loc, value: Exp, body: Stmt}
  Log{event: String, topics: List<&2, IR.Expr>, data: Exp, body: Stmt}
  Check{cond: Exp, body: Stmt}
  Result{value: Exp}
  Stop{}
  Revert{}

# Yul comparisons return the word 1 or 0.
def bit(c: Bool) -> Nat:
  Bool.pick(Nat, c, 1n, 0n)

# EVM arithmetic modulo the limit. On words below the limit these are the
# EVM's operations. Above it the EVM has no words, so the model picks results
# that make the overflow check revert, and the proof needs no range invariant.
def add(+x: Nat, +y: Nat, +l: Nat) -> Nat:
  +s = Nat.add(x, y)
  Bool.pick(Nat, Nat.is_lt(s, l), s, Nat.sub(s, l))

# When x >= y this is x - y for any x, which checked sub needs.
def sub(+x: Nat, +y: Nat, +l: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(x, y), Bool.pick(Nat, Nat.is_lt(y, l), Nat.sub(l, Nat.sub(y, x)), l), Nat.sub(x, y))

def not(+x: Nat, +l: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(x, l), Nat.sub(Nat.sub(l, 1n), x), l)

def gt(+x: Nat, +y: Nat, +l: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(y, l), bit(Nat.is_lt(y, x)), 1n)

def eval(e: Exp, +env: List<&2, IR.Binding>, +s: Evm.State) -> Nat:
  match e:
    case Atom{value}:
      IR.eval(value, env)
    case SLoad{loc}:
      Evm.lookup(Evm.storage.of(s), IR.loc(loc, env))
    case Caller{}:
      Evm.caller.of(s)
    case Add{left, right}:
      a b = eval(left, env, s) eval(right, env, s)
      add(a, b, Evm.limit.of(s))
    case Sub{left, right}:
      a b = eval(left, env, s) eval(right, env, s)
      sub(a, b, Evm.limit.of(s))
    case Not{value}:
      not(eval(value, env, s), Evm.limit.of(s))
    case Eq{left, right}:
      a b = eval(left, env, s) eval(right, env, s)
      bit(Nat.is_eq(a, b))
    case Lt{left, right}:
      a b = eval(left, env, s) eval(right, env, s)
      bit(Nat.is_lt(a, b))
    case Gt{left, right}:
      a b = eval(left, env, s) eval(right, env, s)
      gt(a, b, Evm.limit.of(s))
    case IsZero{value}:
      bit(Nat.is_eq(eval(value, env, s), 0n))

# `if cond { revert(0, 0) }` reverts when cond is not zero.
def exec(stmt: Stmt, +out: IR.Output, +env: List<&2, IR.Binding>) -> Evm.Contract(IR.value(out)):
  match stmt out:
    case Let{level, value, body} o:
      R => k => +s => exec(body, o, IR.Binding{level, eval(value, env, s)} <> env, R, k, s)
    case SStore{loc, value, body} o:
      R => k => +s => exec(body, o, env, R, k, Evm.write.go(IR.loc(loc, env), eval(value, env, s), s))
    case Log{event, topics, data, body} o:
      R => k => +s => exec(body, o, env, R, k, Evm.log.go(event, IR.evals(topics, env), eval(data, env, s), s))
    case Check{cond, body} o:
      R => k => +s => Bool.pick(Evm.Outcome<R>, Nat.is_eq(eval(cond, env, s), 0n), exec(body, o, env, R, k, s), Evm.Revert{})
    case Result{value} IR.Returns{}:
      R => k => +s => k(eval(value, env, s), s)
    case Stop{} IR.Stops{}:
      R => k => s => k(Unit{}, s)
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
# Checked sub reverts when a < b.
def overflow(+left: IR.Expr, +right: IR.Expr) -> Exp:
  Gt{Atom{right}, Sub{Not{Atom{IR.Lit{0n}}}, Atom{left}}}

# The entry's output is known, so a tail of the wrong kind lowers to a revert.
def lower(cmd: IR.Cmd, +out: IR.Output) -> Stmt:
  match cmd out:
    case IR.Bind{IR.SLoad{loc}, level, body} o:
      Let{level, SLoad{loc}, lower(body, o)}
    case IR.Bind{IR.Caller{}, level, body} o:
      Let{level, Caller{}, lower(body, o)}
    case IR.Bind{IR.Add{+left, +right}, level, body} o:
      Check{overflow(left, right), Let{level, Add{Atom{left}, Atom{right}}, lower(body, o)}}
    case IR.Bind{IR.Sub{+left, +right}, level, body} o:
      Check{Lt{Atom{left}, Atom{right}}, Let{level, Sub{Atom{left}, Atom{right}}, lower(body, o)}}
    case IR.Then{IR.SStore{loc, value}, body} o:
      SStore{loc, Atom{value}, lower(body, o)}
    case IR.Then{IR.Log{event, topics, data}, body} o:
      Log{event, topics, Atom{data}, lower(body, o)}
    case IR.Then{IR.Require{c}, body} o:
      Check{lower.cond(c), lower(body, o)}
    case IR.Return{value} IR.Returns{}:
      Result{Atom{value}}
    case IR.Tail{IR.SLoad{loc}} IR.Returns{}:
      Result{SLoad{loc}}
    case IR.Tail{IR.Caller{}} IR.Returns{}:
      Result{Caller{}}
    case IR.Tail{IR.Add{+left, +right}} IR.Returns{}:
      Check{overflow(left, right), Result{Add{Atom{left}, Atom{right}}}}
    case IR.Tail{IR.Sub{+left, +right}} IR.Returns{}:
      Check{Lt{Atom{left}, Atom{right}}, Result{Sub{Atom{left}, Atom{right}}}}
    case IR.Finish{IR.SStore{loc, value}} IR.Stops{}:
      SStore{loc, Atom{value}, Stop{}}
    case IR.Finish{IR.Log{event, topics, data}} IR.Stops{}:
      Log{event, topics, Atom{data}, Stop{}}
    case IR.Finish{IR.Require{c}} IR.Stops{}:
      Check{lower.cond(c), Stop{}}
    case IR.Stop{} IR.Stops{}:
      Stop{}
    case _ _:
      Revert{}
