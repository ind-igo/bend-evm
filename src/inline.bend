import Base
import ./ir.bend as IR

# Inlines a call to one of the contract's own functions into the IR. The
# reader uses it, and it is not trusted: the certificate checks the result.
#
# The callee's parameters become the argument expressions. Its other levels
# move above every level of the caller's rest, so no name is captured and Yul
# declares no local twice. Its tail then joins the rest: a returned value
# replaces the bound variable, and a tail action binds it.

type Callee is Data:
  Callee{parameters: List<&2, Nat>, args: List<&2, IR.Expr>, body: IR.Cmd}

def max(+a: Nat, +b: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(a, b), b, a)

def top.expr(e: IR.Expr) -> Nat:
  match e:
    case IR.Lit{_}:
      0n
    case IR.Var{level}:
      level

def top.list(exprs: List<&2, IR.Expr>) -> Nat:
  match exprs:
    case Nil{}:
      0n
    case e <> rest:
      max(top.expr(e), top.list(rest))

def top.two(left: IR.Expr, right: IR.Expr) -> Nat:
  max(top.expr(left), top.expr(right))

def top.cond(c: IR.Cond) -> Nat:
  match c:
    case IR.Eq{left, right}:
      top.two(left, right)
    case IR.Lt{left, right}:
      top.two(left, right)
    case IR.Not{c}:
      top.cond(c)

def top.loc(l: IR.Loc) -> Nat:
  match l:
    case IR.Plain{slot}:
      top.expr(slot)
    case IR.Mapped{base, key}:
      max(top.loc(base), top.expr(key))

def top.word(w: IR.Word) -> Nat:
  match w:
    case IR.SLoad{l}:
      top.loc(l)
    case IR.Caller{}:
      0n
    case IR.Add{left, right}:
      top.two(left, right)
    case IR.Sub{left, right}:
      top.two(left, right)
    case IR.Select{c, yes, no}:
      max(top.cond(c), top.two(yes, no))
    case IR.Keccak{words}:
      top.list(words)
    case IR.Typed{domain, message}:
      top.two(domain, message)
    case IR.Recover{digest, v, r, s}:
      max(top.two(digest, v), top.two(r, s))
    case IR.View{target, _, args}:
      max(top.expr(target), top.list(args))
    case IR.Max{}:
      0n
    case IR.Timestamp{}:
      0n
    case IR.ChainId{}:
      0n
    case IR.Self{}:
      0n
    case IR.Id{_}:
      0n

def top.effect(e: IR.Effect) -> Nat:
  match e:
    case IR.SStore{l, value}:
      max(top.loc(l), top.expr(value))
    case IR.Log{_, topics, data}:
      max(top.list(topics), top.list(data))
    case IR.Require{c}:
      top.cond(c)
    case IR.Ensure{c, _, args}:
      max(top.cond(c), top.list(args))

# The largest level that cmd binds or reads.
def top(cmd: IR.Cmd) -> Nat:
  match cmd:
    case IR.Bind{w, +level, body}:
      max(max(top.word(w), level), top(body))
    case IR.Then{e, body}:
      max(top.effect(e), top(body))
    case IR.Return{v}:
      top.expr(v)
    case IR.Tail{w}:
      top.word(w)
    case IR.Finish{e}:
      top.effect(e)
    case IR.Stop{}:
      0n
    case IR.If{c, yes, no}:
      max(top.cond(c), max(top(yes), top(no)))

# A level is a parameter, replaced by its argument, or moves up by offset.
def rename.var(+level: Nat, parameters: List<&2, Nat>, args: List<&2, IR.Expr>, +offset: Nat) -> IR.Expr:
  match parameters args:
    case +p <> ps a <> rest:
      Bool.pick(IR.Expr, Nat.is_eq(p, level), a, rename.var(level, ps, rest, offset))
    case _ _:
      IR.Var{Nat.add(level, offset)}

def rename.expr(e: IR.Expr, +parameters: List<&2, Nat>, +args: List<&2, IR.Expr>, +offset: Nat) -> IR.Expr:
  match e:
    case IR.Lit{value}:
      IR.Lit{value}
    case IR.Var{level}:
      rename.var(level, parameters, args, offset)

def rename.list(exprs: List<&2, IR.Expr>, +parameters: List<&2, Nat>, +args: List<&2, IR.Expr>, +offset: Nat) ->
  List<&2, IR.Expr>:
  match exprs:
    case Nil{}:
      Nil{}
    case e <> rest:
      rename.expr(e, parameters, args, offset) <> rename.list(rest, parameters, args, offset)

def rename.cond(c: IR.Cond, +parameters: List<&2, Nat>, +args: List<&2, IR.Expr>, +offset: Nat) -> IR.Cond:
  match c:
    case IR.Eq{left, right}:
      IR.Eq{rename.expr(left, parameters, args, offset), rename.expr(right, parameters, args, offset)}
    case IR.Lt{left, right}:
      IR.Lt{rename.expr(left, parameters, args, offset), rename.expr(right, parameters, args, offset)}
    case IR.Not{c}:
      IR.Not{rename.cond(c, parameters, args, offset)}

def rename.loc(l: IR.Loc, +parameters: List<&2, Nat>, +args: List<&2, IR.Expr>, +offset: Nat) -> IR.Loc:
  match l:
    case IR.Plain{slot}:
      IR.Plain{rename.expr(slot, parameters, args, offset)}
    case IR.Mapped{base, key}:
      IR.Mapped{rename.loc(base, parameters, args, offset), rename.expr(key, parameters, args, offset)}

def rename.word(w: IR.Word, +parameters: List<&2, Nat>, +args: List<&2, IR.Expr>, +offset: Nat) -> IR.Word:
  match w:
    case IR.SLoad{l}:
      IR.SLoad{rename.loc(l, parameters, args, offset)}
    case IR.Caller{}:
      IR.Caller{}
    case IR.Add{left, right}:
      IR.Add{rename.expr(left, parameters, args, offset), rename.expr(right, parameters, args, offset)}
    case IR.Sub{left, right}:
      IR.Sub{rename.expr(left, parameters, args, offset), rename.expr(right, parameters, args, offset)}
    case IR.Select{c, yes, no}:
      IR.Select{rename.cond(c, parameters, args, offset), rename.expr(yes, parameters, args, offset),
        rename.expr(no, parameters, args, offset)}
    case IR.Max{}:
      IR.Max{}
    case IR.Timestamp{}:
      IR.Timestamp{}
    case IR.ChainId{}:
      IR.ChainId{}
    case IR.Self{}:
      IR.Self{}
    case IR.Keccak{words}:
      IR.Keccak{rename.list(words, parameters, args, offset)}
    case IR.Typed{domain, message}:
      IR.Typed{rename.expr(domain, parameters, args, offset), rename.expr(message, parameters, args, offset)}
    case IR.Id{text}:
      IR.Id{text}
    case IR.Recover{digest, v, r, s}:
      IR.Recover{rename.expr(digest, parameters, args, offset), rename.expr(v, parameters, args, offset),
        rename.expr(r, parameters, args, offset), rename.expr(s, parameters, args, offset)}
    case IR.View{target, signature, words}:
      IR.View{rename.expr(target, parameters, args, offset), signature, rename.list(words, parameters, args, offset)}

def rename.effect(e: IR.Effect, +parameters: List<&2, Nat>, +args: List<&2, IR.Expr>, +offset: Nat) -> IR.Effect:
  match e:
    case IR.SStore{l, value}:
      IR.SStore{rename.loc(l, parameters, args, offset), rename.expr(value, parameters, args, offset)}
    case IR.Log{event, topics, data}:
      IR.Log{event, rename.list(topics, parameters, args, offset), rename.list(data, parameters, args, offset)}
    case IR.Require{c}:
      IR.Require{rename.cond(c, parameters, args, offset)}
    case IR.Ensure{c, error, words}:
      IR.Ensure{rename.cond(c, parameters, args, offset), error, rename.list(words, parameters, args, offset)}

def rename(cmd: IR.Cmd, +parameters: List<&2, Nat>, +args: List<&2, IR.Expr>, +offset: Nat) -> IR.Cmd:
  match cmd:
    case IR.Bind{w, level, body}:
      IR.Bind{rename.word(w, parameters, args, offset), Nat.add(level, offset), rename(body, parameters, args, offset)}
    case IR.Then{e, body}:
      IR.Then{rename.effect(e, parameters, args, offset), rename(body, parameters, args, offset)}
    case IR.Return{v}:
      IR.Return{rename.expr(v, parameters, args, offset)}
    case IR.Tail{w}:
      IR.Tail{rename.word(w, parameters, args, offset)}
    case IR.Finish{e}:
      IR.Finish{rename.effect(e, parameters, args, offset)}
    case IR.Stop{}:
      IR.Stop{}
    case IR.If{c, yes, no}:
      IR.If{rename.cond(c, parameters, args, offset), rename(yes, parameters, args, offset), rename(no, parameters, args, offset)}

# Substitutes value for the variable at level: a rename with one parameter
# and offset 0.
def subst(cmd: IR.Cmd, +level: Nat, +value: IR.Expr) -> IR.Cmd:
  rename(cmd, [level], [value], 0n)

# The callee's body, renamed to sit above every level up to bound.
def place(k: Callee, +bound: Nat) -> Result<&2, &2, String, IR.Cmd>:
  match k:
    case Callee{+parameters, +args, +body}:
      +offset = Nat.add(1n, max(bound, max(top(body), top.list(args))))
      Bool.pick(Result<&2, &2, String, IR.Cmd>,
        Nat.is_eq(List.length(&2, Nat, parameters), List.length(&2, IR.Expr, args)),
        Done{rename(body, parameters, args, offset)},
        Fail{"A call must pass every parameter"})

# Joins a callee that returns a word to the rest, which reads it at level.
def splice.word(callee: IR.Cmd, +level: Nat, +rest: IR.Cmd) -> Result<&2, &2, String, IR.Cmd>:
  match callee:
    case IR.Bind{w, l, body}:
      do Result<&2, &2, String, IR.Cmd>:
        b : IR.Cmd <- splice.word(body, level, rest)
        return IR.Bind{w, l, b}
    case IR.Then{e, body}:
      do Result<&2, &2, String, IR.Cmd>:
        b : IR.Cmd <- splice.word(body, level, rest)
        return IR.Then{e, b}
    case IR.Return{v}:
      Done{subst(rest, level, v)}
    case IR.Tail{w}:
      Done{IR.Bind{w, level, rest}}
    case IR.If{_, _, _}:
      Fail{"A call to a function that branches must be the last step"}
    case _:
      Fail{"A called function returns Unit where a word is bound"}

# Joins a callee that returns Unit to the rest.
def splice.unit(callee: IR.Cmd, +rest: IR.Cmd) -> Result<&2, &2, String, IR.Cmd>:
  match callee:
    case IR.Bind{w, l, body}:
      do Result<&2, &2, String, IR.Cmd>:
        b : IR.Cmd <- splice.unit(body, rest)
        return IR.Bind{w, l, b}
    case IR.Then{e, body}:
      do Result<&2, &2, String, IR.Cmd>:
        b : IR.Cmd <- splice.unit(body, rest)
        return IR.Then{e, b}
    case IR.Finish{e}:
      Done{IR.Then{e, rest}}
    case IR.Stop{}:
      Done{rest}
    case IR.If{_, _, _}:
      Fail{"A call to a function that branches must be the last step"}
    case _:
      Fail{"A called function returns a word where Unit is expected"}
