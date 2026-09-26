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
  Select{cond: Exp, yes: Exp, no: Exp}
  Timestamp{}
  ChainId{}
  Address{}
  Keccak{words: List<&2, IR.Expr>}
  Typed{domain: IR.Expr, message: IR.Expr}
  Id{text: String}
  Recover{digest: IR.Expr, v: IR.Expr, r: IR.Expr, sig: IR.Expr}

# Each statement holds the rest of its block, so a block is one Stmt.
type Stmt is Data:
  Let{level: Nat, value: Exp, body: Stmt}
  SStore{loc: IR.Loc, value: Exp, body: Stmt}
  Log{event: String, topics: List<&2, IR.Expr>, data: List<&2, IR.Expr>, body: Stmt}
  Check{cond: Exp, body: Stmt}
  Guard{cond: Exp, error: String, args: List<&2, IR.Expr>, body: Stmt}
  View{level: Nat, target: IR.Expr, signature: String, args: List<&2, IR.Expr>, body: Stmt}
  Answer{target: IR.Expr, signature: String, args: List<&2, IR.Expr>}
  Result{value: Exp}
  Stop{}
  Revert{}
  If{test: Exp, yes: Stmt, no: Stmt}

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
    case Select{cond, yes, no}:
      c y n = eval(cond, env, s) eval(yes, env, s) eval(no, env, s)
      Bool.pick(Nat, Nat.is_eq(c, 0n), n, y)
    case Timestamp{}:
      Evm.time.of(Evm.world.of(s))
    case ChainId{}:
      Evm.chain.of(Evm.world.of(s))
    case Address{}:
      Evm.self.of(Evm.world.of(s))
    case Keccak{words}:
      Evm.hash.of(Evm.hashes.of(Evm.world.of(s)), Evm.Words{IR.evals(words, env)})
    case Typed{domain, message}:
      Evm.hash.of(Evm.hashes.of(Evm.world.of(s)), Evm.Typed{IR.eval(domain, env), IR.eval(message, env)})
    case Id{text}:
      Evm.hash.of(Evm.hashes.of(Evm.world.of(s)), Evm.Text{text})
    case Recover{digest, v, r, sig}:
      Evm.signer.of(Evm.signers.of(Evm.world.of(s)), IR.eval(digest, env), IR.eval(v, env), IR.eval(r, env), IR.eval(sig, env))

# `if cond { revert(0, 0) }` reverts when cond is not zero, and a Guard
# reverts with its error's data. A View binds a staticcall's word, and an
# Answer returns it. An If runs no when its test is zero and yes otherwise.
def exec(stmt: Stmt, +out: IR.Output, +env: List<&2, IR.Binding>) -> Evm.Contract(IR.value(out)):
  match stmt out:
    case Let{level, value, body} o:
      R => k => +s => exec(body, o, IR.Binding{level, eval(value, env, s)} <> env, R, k, s)
    case SStore{loc, value, body} o:
      R => k => +s => exec(body, o, env, R, k, Evm.write.go(IR.loc(loc, env), eval(value, env, s), s))
    case Log{event, topics, data, body} o:
      R => k => +s => exec(body, o, env, R, k, Evm.log.go(IR.name(event), IR.evals(topics, env), IR.evals(data, env), s))
    case Check{cond, body} o:
      R => k => +s => Bool.pick(Evm.Outcome<R>, Nat.is_eq(eval(cond, env, s), 0n), exec(body, o, env, R, k, s), Evm.Revert{})
    case Guard{cond, error, args, body} o:
      R => k => +s => Bool.pick(Evm.Outcome<R>, Nat.is_eq(eval(cond, env, s), 0n), exec(body, o, env, R, k, s),
        Evm.Raise{Evm.Error{IR.name(error), IR.evals(args, env)}})
    case View{level, target, signature, args, body} o:
      R => k => Evm.view(Evm.Call{IR.eval(target, env), IR.name(signature), IR.evals(args, env)}, R,
        x => exec(body, o, IR.Binding{level, x} <> env, R, k))
    case Answer{target, signature, args} IR.Returns{}:
      Evm.view(Evm.Call{IR.eval(target, env), IR.name(signature), IR.evals(args, env)})
    case Result{value} IR.Returns{}:
      R => k => +s => k(eval(value, env, s), s)
    case Stop{} IR.Stops{}:
      R => k => s => k(Unit{}, s)
    case If{test, yes, no} o:
      R => k => +s => Evm.branch(IR.value(o), Nat.is_eq(eval(test, env, s), 0n), exec(no, o, env), exec(yes, o, env), R, k, s)
    case _ o:
      IR.abort(IR.value(o))

# A test that is 1 when the condition holds and 0 when it does not.
def lower.test(c: IR.Cond) -> Exp:
  match c:
    case IR.Eq{left, right}:
      Eq{Atom{left}, Atom{right}}
    case IR.Lt{left, right}:
      Lt{Atom{left}, Atom{right}}
    case IR.Not{c}:
      IsZero{lower.test(c)}

# The condition under which a Require reverts.
def lower.cond(c: IR.Cond) -> Exp:
  IsZero{lower.test(c)}

def lower.select(c: IR.Cond, +yes: IR.Expr, +no: IR.Expr) -> Exp:
  Select{lower.test(c), Atom{yes}, Atom{no}}

def max() -> Exp:
  Not{Atom{IR.Lit{0n}}}

# Checked add reverts when b > not(0) - a, that is when a + b overflows.
def overflow(+left: IR.Expr, +right: IR.Expr) -> Exp:
  Gt{Atom{right}, Sub{max(), Atom{left}}}

# A word as a Yul expression. Checked add and sub also need a check, which
# lower adds before them.
def lower.word(w: IR.Word) -> Exp:
  match w:
    case IR.SLoad{loc}:
      SLoad{loc}
    case IR.Caller{}:
      Caller{}
    case IR.Add{left, right}:
      Add{Atom{left}, Atom{right}}
    case IR.Sub{left, right}:
      Sub{Atom{left}, Atom{right}}
    case IR.Select{c, yes, no}:
      lower.select(c, yes, no)
    case IR.Max{}:
      max()
    case IR.Timestamp{}:
      Timestamp{}
    case IR.ChainId{}:
      ChainId{}
    case IR.Self{}:
      Address{}
    case IR.Keccak{words}:
      Keccak{words}
    case IR.Typed{domain, message}:
      Typed{domain, message}
    case IR.Id{text}:
      Id{text}
    case IR.Recover{digest, v, r, sig}:
      Recover{digest, v, r, sig}
    case IR.View{_, _, _}:
      # A call can revert, so it is no expression: lower makes it a View or
      # an Answer, and never gets here.
      Atom{IR.Lit{0n}}

# The entry's output is known, so a tail of the wrong kind lowers to a revert.
def lower(cmd: IR.Cmd, +out: IR.Output) -> Stmt:
  match cmd out:
    case IR.Bind{IR.Add{+left, +right}, level, body} o:
      Check{overflow(left, right), Let{level, Add{Atom{left}, Atom{right}}, lower(body, o)}}
    case IR.Bind{IR.Sub{+left, +right}, level, body} o:
      Check{Lt{Atom{left}, Atom{right}}, Let{level, Sub{Atom{left}, Atom{right}}, lower(body, o)}}
    case IR.Bind{IR.View{target, signature, args}, level, body} o:
      View{level, target, signature, args, lower(body, o)}
    case IR.Bind{w, level, body} o:
      Let{level, lower.word(w), lower(body, o)}
    case IR.Then{IR.SStore{loc, value}, body} o:
      SStore{loc, Atom{value}, lower(body, o)}
    case IR.Then{IR.Log{event, topics, data}, body} o:
      Log{event, topics, data, lower(body, o)}
    case IR.Then{IR.Require{c}, body} o:
      Check{lower.cond(c), lower(body, o)}
    case IR.Then{IR.Ensure{c, error, args}, body} o:
      Guard{lower.cond(c), error, args, lower(body, o)}
    case IR.Return{value} IR.Returns{}:
      Result{Atom{value}}
    case IR.Tail{IR.Add{+left, +right}} IR.Returns{}:
      Check{overflow(left, right), Result{Add{Atom{left}, Atom{right}}}}
    case IR.Tail{IR.Sub{+left, +right}} IR.Returns{}:
      Check{Lt{Atom{left}, Atom{right}}, Result{Sub{Atom{left}, Atom{right}}}}
    case IR.Tail{IR.View{target, signature, args}} IR.Returns{}:
      Answer{target, signature, args}
    case IR.Tail{w} IR.Returns{}:
      Result{lower.word(w)}
    case IR.Finish{IR.SStore{loc, value}} IR.Stops{}:
      SStore{loc, Atom{value}, Stop{}}
    case IR.Finish{IR.Log{event, topics, data}} IR.Stops{}:
      Log{event, topics, data, Stop{}}
    case IR.Finish{IR.Require{c}} IR.Stops{}:
      Check{lower.cond(c), Stop{}}
    case IR.Finish{IR.Ensure{c, error, args}} IR.Stops{}:
      Guard{lower.cond(c), error, args, Stop{}}
    case IR.Stop{} IR.Stops{}:
      Stop{}
    case IR.If{c, yes, no} o:
      If{lower.test(c), lower(yes, o), lower(no, o)}
    case _ _:
      Revert{}
