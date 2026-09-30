import Base
import ./Evm.bend as Evm
import ./ir.bend as IR
import ./yul.bend as Yul
import ./calls.bend as Calls
import ./LAWS.bend as Laws
import ./nat.bend as N

# Nat facts for the overflow checks.

# a <= p, so p < a is false.
def flip(+a: Nat, +p: Nat, +e: {True{} == Nat.is_lt(a, 1n+p) : Bool}) -> {False{} == Nat.is_lt(p, a) : Bool}:
  %Equal.sym(Bool, True{}, Nat.is_lt(a, 1n+p), e) : {Bool.not(_) == Nat.is_lt(p, a) : Bool}
  N.lt_flip(p, a)

# p < a + 1 fails, so p < a.
def lt_over(+a: Nat, +p: Nat, +e: {False{} == Nat.is_lt(a, 1n+p) : Bool}) -> {True{} == Nat.is_lt(p, a) : Bool}:
  %Equal.sym(Bool, False{}, Nat.is_lt(a, 1n+p), e) : {Bool.not(_) == Nat.is_lt(p, a) : Bool}
  N.lt_flip(p, a)

# The heart of the check: for a <= p, p - a < b exactly when a + b >= p + 1.
def sub_check(+a: Nat, +p: Nat, +b: Nat, +e: {True{} == Nat.is_lt(a, 1n+p) : Bool}) ->
  {Bool.not(Nat.is_lt(Nat.add(a, b), 1n+p)) == Nat.is_lt(Nat.sub(p, a), b) : Bool}:
  match a p:
    case 0n +q:
      %N.sub_zero(q) : {Bool.not(Nat.is_lt(b, 1n+q)) == Nat.is_lt(_, b) : Bool}
      N.lt_flip(q, b)
    case 1n+(+c) 0n:
      N.absurd({Bool.not(Nat.is_lt(Nat.add(1n+c, b), 1n)) == Nat.is_lt(Nat.sub(0n, 1n+c), b) : Bool}, N.no_lt_zero(c, e))
    case 1n+(+c) 1n+(+q):
      sub_check(c, q, b, e)

def zero_of_not(+c: Bool) -> {c == Nat.is_eq(Yul.bit(Bool.not(c)), 0n) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def not_zero(+p: Nat) -> {p == Yul.not(0n, 1n+p) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+_:
      {==}

def sub_in(+p: Nat, +a: Nat, +e: {True{} == Nat.is_lt(a, 1n+p) : Bool}) -> {Nat.sub(p, a) == Yul.sub(p, a, 1n+p) : Nat}:
  %flip(a, p, e) : {Nat.sub(p, a) == Bool.pick(Nat, _,
    Bool.pick(Nat, Nat.is_lt(a, 1n+p), Nat.sub(1n+p, Nat.sub(a, p)), 1n+p), Nat.sub(p, a)) : Nat}
  {==}

def sub_out(+p: Nat, +a: Nat, +e: {False{} == Nat.is_lt(a, 1n+p) : Bool}) -> {1n+p == Yul.sub(p, a, 1n+p) : Nat}:
  %e : {1n+p == Bool.pick(Nat, Nat.is_lt(p, a),
    Bool.pick(Nat, _, Nat.sub(1n+p, Nat.sub(a, p)), 1n+p), Nat.sub(p, a)) : Nat}
  %lt_over(a, p, e) : {1n+p == Bool.pick(Nat, _,
    Bool.pick(Nat, False{}, Nat.sub(1n+p, Nat.sub(a, p)), 1n+p), Nat.sub(p, a)) : Nat}
  {==}

def gt_in(+b: Nat, +x: Nat, +l: Nat, +e: {True{} == Nat.is_lt(x, l) : Bool}) -> {Yul.bit(Nat.is_lt(x, b)) == Yul.gt(b, x, l) : Nat}:
  %e : {Yul.bit(Nat.is_lt(x, b)) == Bool.pick(Nat, _, Yul.bit(Nat.is_lt(x, b)), 1n) : Nat}
  {==}

def gt_out(+b: Nat, +l: Nat) -> {1n == Yul.gt(b, l, l) : Nat}:
  %N.lt_irrefl(l) : {1n == Bool.pick(Nat, _, Yul.bit(Nat.is_lt(l, b)), 1n) : Nat}
  {==}

def guard.succ(+a: Nat, +b: Nat, +p: Nat, +c: Bool, +e: {c == Nat.is_lt(a, 1n+p) : Bool}) ->
  {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(Yul.gt(b, Yul.sub(p, a, 1n+p), 1n+p), 0n) : Bool}:
  match c:
    case True{}:
      %sub_in(p, a, e) : {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(Yul.gt(b, _, 1n+p), 0n) : Bool}
      %gt_in(b, Nat.sub(p, a), 1n+p, N.sub_lt_succ(p, a)) : {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(_, 0n) : Bool}
      %sub_check(a, p, b, e) : {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(Yul.bit(_), 0n) : Bool}
      zero_of_not(Nat.is_lt(Nat.add(a, b), 1n+p))
    case False{}:
      %sub_out(p, a, e) : {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(Yul.gt(b, _, 1n+p), 0n) : Bool}
      %gt_out(b, 1n+p) : {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(_, 0n) : Bool}
      %N.add_ge(a, b, 1n+p, e) : {_ == False{} : Bool}
      {==}

# The overflow check `gt(b, sub(not(0), a))` is zero exactly when a + b < limit.
def guard(+a: Nat, +b: Nat, +l: Nat) -> {Nat.is_lt(Nat.add(a, b), l) == Nat.is_eq(Yul.gt(b, Yul.sub(Yul.not(0n, l), a, l), l), 0n) : Bool}:
  match l:
    case 0n:
      %N.lt_zero(Yul.sub(Yul.not(0n, 0n), a, 0n)) : {Nat.is_lt(Nat.add(a, b), 0n)
        == Nat.is_eq(Bool.pick(Nat, _, Yul.bit(Nat.is_lt(Yul.sub(Yul.not(0n, 0n), a, 0n), b)), 1n), 0n) : Bool}
      Equal.sym(Bool, False{}, Nat.is_lt(Nat.add(a, b), 0n), N.lt_zero(Nat.add(a, b)))
    case 1n+(+p):
      %not_zero(p) : {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(Yul.gt(b, Yul.sub(_, a, 1n+p), 1n+p), 0n) : Bool}
      guard.succ(a, b, p, Nat.is_lt(a, 1n+p), {==})

# The overflow check of checked mul, as the Yul model computes it.
def mul.check(+a: Nat, +b: Nat, +l: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_eq(l, 0n), 1n, Evm.bitwise(Evm.And{}, Yul.bit(Nat.is_eq(Yul.bit(Nat.is_eq(a, 0n)), 0n)),
    Yul.gt(b, Bool.pick(Nat, Nat.is_eq(a, 0n), 0n, Nat.div(Yul.not(0n, l), a)), l)))

def and_bit(+c: Bool) -> {Bool.not(c) == Nat.is_eq(Evm.bitwise(Evm.And{}, 1n, Yul.bit(c)), 0n) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def mul_guard.at(a: Nat, +b: Nat, +p: Nat) -> {Nat.is_lt(Nat.mul(a, b), 1n+p) == Nat.is_eq(mul.check(a, b, 1n+p), 0n) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+_:
      {==}
    case 1n+(+q) +c:
      +d = Nat.div(p, 1n+q)
      %N.floor(q, c, p) : {_ == Nat.is_eq(mul.check(1n+q, c, 1n+p), 0n) : Bool}
      %not_zero(p) : {Bool.not(Nat.is_lt(d, c)) == Nat.is_eq(Evm.bitwise(Evm.And{}, 1n, Yul.gt(c, Nat.div(_, 1n+q), 1n+p)), 0n) : Bool}
      %N.div_le(p, q) : {Bool.not(Nat.is_lt(d, c)) ==
        Nat.is_eq(Evm.bitwise(Evm.And{}, 1n, Bool.pick(Nat, _, Yul.bit(Nat.is_lt(d, c)), 1n)), 0n) : Bool}
      and_bit(Nat.is_lt(d, c))

# The check `and(iszero(iszero(a)), gt(b, div(not(0), a)))` is zero exactly
# when a * b < limit.
def mul_guard(+a: Nat, +b: Nat, +l: Nat) -> {Nat.is_lt(Nat.mul(a, b), l) == Nat.is_eq(mul.check(a, b, l), 0n) : Bool}:
  match l:
    case 0n:
      %N.lt_zero(Nat.mul(a, b)) : {_ == False{} : Bool}
      {==}
    case 1n+(+p):
      mul_guard.at(a, b, p)

def mod_in(+x: Nat, +l: Nat, +e: {True{} == Nat.is_lt(x, l) : Bool}) -> {x == Nat.mod(x, l) : Nat}:
  match l:
    case 0n:
      N.absurd({x == Nat.mod(x, 0n) : Nat}, N.no_lt_zero(x, e))
    case 1n+(+q):
      N.mod_small(x, q, e)

# Checked mul: the check passes exactly when Evm.mul does, and then the
# wrapping product is the product.
def mul_step(+prod: Nat, +l: Nat, c: Bool, v: Bool, g: {c == v : Bool}, +ec: {c == Nat.is_lt(prod, l) : Bool}, -R: Data,
  -y: Nat -> Evm.Outcome<R>, -f: Nat -> Evm.Outcome<R>, -d: Evm.Outcome<R> -> Evm.Outcome<R>,
  h: {d(y(prod)) == d(f(prod)) : Evm.Outcome<R>}) ->
  {d(Bool.pick(Evm.Outcome<R>, v, y(Nat.mod(prod, l)), Evm.Revert{})) == d(Bool.pick(Evm.Outcome<R>, c, f(prod), Evm.Revert{})) : Evm.Outcome<R>}:
  match c:
    case True{}:
      %g : {d(Bool.pick(Evm.Outcome<R>, _, y(Nat.mod(prod, l)), Evm.Revert{})) == d(f(prod)) : Evm.Outcome<R>}
      %mod_in(prod, l, ec) : {d(y(_)) == d(f(prod)) : Evm.Outcome<R>}
      h
    case False{}:
      %g : {d(Bool.pick(Evm.Outcome<R>, _, y(Nat.mod(prod, l)), Evm.Revert{})) == d(Evm.Revert{}) : Evm.Outcome<R>}
      {==}

# The lemmas compare two outcomes as d sees them, where d runs an outcome
# with the answers and callbacks of calls.bend. d is the same on both sides,
# so a revert on both sides agrees.

# Checked add: the guard passes exactly when Evm.add does, and then wrapping
# add is the plain sum. y and f are the rest of the Yul and IR runs.
def add_step(c: Bool, v: Bool, g: {c == v : Bool}, +sum: Nat, +l: Nat, -R: Data,
  -y: Nat -> Evm.Outcome<R>, -f: Nat -> Evm.Outcome<R>, -d: Evm.Outcome<R> -> Evm.Outcome<R>,
  h: {d(y(Bool.pick(Nat, c, sum, Nat.sub(sum, l)))) == d(f(Bool.pick(Nat, c, sum, Nat.sub(sum, l)))) : Evm.Outcome<R>}) ->
  {d(Bool.pick(Evm.Outcome<R>, v, y(Bool.pick(Nat, c, sum, Nat.sub(sum, l))), Evm.Revert{}))
    == d(Bool.pick(Evm.Outcome<R>, c, f(sum), Evm.Revert{})) : Evm.Outcome<R>}:
  match c:
    case True{}:
      %g : {d(Bool.pick(Evm.Outcome<R>, _, y(sum), Evm.Revert{})) == d(f(sum)) : Evm.Outcome<R>}
      h
    case False{}:
      %g : {d(Bool.pick(Evm.Outcome<R>, _, y(Nat.sub(sum, l)), Evm.Revert{})) == d(Evm.Revert{}) : Evm.Outcome<R>}
      {==}

# Checked sub: `if lt(a, b)` reverts exactly when Evm.sub does, and when it
# passes, Yul.sub is a - b.
def sub_step(c: Bool, -x: Nat, +n: Nat, -R: Data, -y: Nat -> Evm.Outcome<R>, -f: Nat -> Evm.Outcome<R>,
  -d: Evm.Outcome<R> -> Evm.Outcome<R>, h: {d(y(Bool.pick(Nat, c, x, n))) == d(f(Bool.pick(Nat, c, x, n))) : Evm.Outcome<R>}) ->
  {d(Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(c), 0n), y(Bool.pick(Nat, c, x, n)), Evm.Revert{}))
    == d(Bool.pick(Evm.Outcome<R>, c, Evm.Revert{}, f(n))) : Evm.Outcome<R>}:
  match c:
    case True{}:
      {==}
    case False{}:
      h

# A Require or an Ensure: iszero(cond) fails with x exactly when the
# condition is false.
def require_step(c: Bool, -R: Data, -x: Evm.Outcome<R>, -y: Evm.Outcome<R>, -f: Evm.Outcome<R>,
  -d: Evm.Outcome<R> -> Evm.Outcome<R>, h: {d(y) == d(f) : Evm.Outcome<R>}) ->
  {d(Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(Nat.is_eq(Yul.bit(c), 0n)), 0n), y, x))
    == d(Bool.pick(Evm.Outcome<R>, c, f, x)) : Evm.Outcome<R>}:
  match c:
    case True{}:
      h
    case False{}:
      {==}

# A Select: Yul's `select(test, a, b)` picks a exactly when the condition holds.
def select_eq(c: Bool, -y: Nat, -n: Nat) -> {Bool.pick(Nat, c, y, n) == Bool.pick(Nat, Nat.is_eq(Yul.bit(c), 0n), n, y) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# Max: `not(0)` is limit - 1.
def max_eq(+l: Nat) -> {Nat.sub(l, 1n) == Yul.not(0n, l) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+(+p):
      match p:
        case 0n:
          {==}
        case 1n+_:
          {==}

# `iszero(test)` inverts a test, so a Not lowers to it.
def bit_of_not(+x: Bool) -> {Yul.bit(Bool.not(x)) == Yul.bit(Nat.is_eq(Yul.bit(x), 0n)) : Nat}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# A lowered test is 1 exactly when the condition holds.
def test_bit(c: IR.Cond, +env: List<&2, IR.Binding>, +s: Evm.State) -> {Yul.bit(IR.cond(c, env)) == Yul.eval(Yul.lower.test(c), env, s) : Nat}:
  match c:
    case IR.Eq{_, _}:
      {==}
    case IR.Lt{_, _}:
      {==}
    case IR.Not{+d}:
      %test_bit(d, env, s) : {Yul.bit(Bool.not(IR.cond(d, env))) == Yul.bit(Nat.is_eq(_, 0n)) : Nat}
      bit_of_not(IR.cond(d, env))

# An If: the lowered test is zero exactly when the condition fails, so Yul
# runs the arm that the IR runs.
def if_step(c: Bool, -n: Nat, e: {Yul.bit(c) == n : Nat}, -A: Data, -R: Data, -ya: Evm.Contract(A), -yb: Evm.Contract(A),
  -ia: Evm.Contract(A), -ib: Evm.Contract(A), -k: A -> Evm.State -> Evm.Outcome<R>, +s: Evm.State,
  -d: Evm.Outcome<R> -> Evm.Outcome<R>,
  ha: {d(ya(R, k, s)) == d(ia(R, k, s)) : Evm.Outcome<R>}, hb: {d(yb(R, k, s)) == d(ib(R, k, s)) : Evm.Outcome<R>}) ->
  {d(Evm.branch(A, Nat.is_eq(n, 0n), yb, ya, R, k, s)) == d(Evm.branch(A, c, ia, ib, R, k, s)) : Evm.Outcome<R>}:
  match c:
    case True{}:
      %e : {d(Evm.branch(A, Nat.is_eq(_, 0n), yb, ya, R, k, s)) == d(ia(R, k, s)) : Evm.Outcome<R>}
      ha
    case False{}:
      %e : {d(Evm.branch(A, Nat.is_eq(_, 0n), yb, ya, R, k, s)) == d(ib(R, k, s)) : Evm.Outcome<R>}
      hb

# The same pick of two outcomes that d sees as equal.
def pick_step(b: Bool, -R: Data, -y: Evm.Outcome<R>, -f: Evm.Outcome<R>, -x: Evm.Outcome<R>,
  -d: Evm.Outcome<R> -> Evm.Outcome<R>, h: {d(y) == d(f) : Evm.Outcome<R>}) ->
  {d(Bool.pick(Evm.Outcome<R>, b, y, x)) == d(Bool.pick(Evm.Outcome<R>, b, f, x)) : Evm.Outcome<R>}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

# A View: Yul and the IR make the same call, and their continuations agree
# on every answer and state, so the outcomes agree.
def view_step(+c: Evm.Call, -R: Data, -y: Nat -> Evm.State -> Evm.Outcome<R>, -f: Nat -> Evm.State -> Evm.Outcome<R>,
  +s: Evm.State, -d: Evm.Outcome<R> -> Evm.Outcome<R>, h: @x: Nat -> @t: Evm.State -> {d(y(x, t)) == d(f(x, t)) : Evm.Outcome<R>}) ->
  {d(Evm.answer(R, c, y, s)) == d(Evm.answer(R, c, f, s)) : Evm.Outcome<R>}:
  match s:
    case Evm.State{storage, caller, limit, logs, Evm.World{facts, readings, self, hashes, signers, answers}}:
      match answers:
        case Nil{}:
          {==}
        case Evm.Answer{q, x} <> rest:
          +t : Evm.State = Evm.State{storage, caller, limit, logs, Evm.World{facts, readings, self, hashes, signers, rest}}
          pick_step(Evm.same.call(q, c), R, y(x, t), f(x, t), Evm.Revert{}, d, h(x, t))

# A Call: Yul and the IR stop at the same call. The run takes the same
# answer and the same callbacks for both, and their continuations agree on
# every later answers, word and state.
def call_step(+c: Evm.Call, -R: Data, -y: Nat -> Evm.State -> Evm.Outcome<R>, -f: Nat -> Evm.State -> Evm.Outcome<R>,
  +s: Evm.State, +entries: List<&2, Calls.Entry>, +steps: List<&2, Calls.Step>, +open: Bool,
  h: @rest: List<&2, Calls.Step> -> @x: Nat -> @t: Evm.State ->
    {Calls.drive(Calls.Model{}, entries, rest, R, False{}, y(x, t)) == Calls.drive(Calls.Model{}, entries, rest, R, False{}, f(x, t)) : Evm.Outcome<R>}) ->
  {Calls.drive(Calls.Model{}, entries, steps, R, open, Evm.Calling{c, s, y})
    == Calls.drive(Calls.Model{}, entries, steps, R, open, Evm.Calling{c, s, f}) : Evm.Outcome<R>}:
  match steps:
    case Nil{}:
      {==}
    case step <> +rest:
      match step:
        case Calls.Enter{_, _, _, _}:
          match open:
            case True{}:
              {==}
            case False{}:
              {==}
        case Calls.Answer{+q, +cbs, +x}:
          match open:
            case True{}:
              {==}
            case False{}:
              +t : Evm.State = Calls.after(Unit, s, Calls.drive(Calls.Model{}, entries, cbs, Unit, True{}, Evm.Ok{Unit{}, s}))
              %h(rest, x, t) : {Bool.pick(Evm.Outcome<R>, Evm.same.call(q, c), Calls.drive(Calls.Model{}, entries, rest, R, False{}, y(x, t)), Evm.Revert{})
                == Bool.pick(Evm.Outcome<R>, Evm.same.call(q, c), _, Evm.Revert{}) : Evm.Outcome<R>}
              {==}

def obs(+entries: List<&2, Calls.Entry>, +steps: List<&2, Calls.Step>, -R: Data, +open: Bool) -> Evm.Outcome<R> -> Evm.Outcome<R>:
  o => Calls.drive(Calls.Model{}, entries, steps, R, open, o)

# Induction on the command. Both runs pass the same state and continuation on,
# so only the checks and ifs need lemmas. The continuation is erased, so an
# If's two arms can both use it.
def sim(+cmd: IR.Cmd, +out: IR.Output, +env: List<&2, IR.Binding>, -R: Data,
  -k: IR.value(out) -> Evm.State -> Evm.Outcome<R>, +s: Evm.State,
  +entries: List<&2, Calls.Entry>, +steps: List<&2, Calls.Step>, +open: Bool) ->
  {Calls.drive(Calls.Model{}, entries, steps, R, open, Yul.exec(Yul.lower(cmd, out), out, env, R, k, s))
    == Calls.drive(Calls.Model{}, entries, steps, R, open, IR.run(cmd, out, env, R, k, s)) : Evm.Outcome<R>}:
  match cmd out:
    case IR.Bind{IR.SLoad{loc}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.lookup(Evm.storage.of(s), IR.loc(loc, env))} <> env, R, k, s, entries, steps, open)
    case IR.Bind{IR.Caller{}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.caller.of(s)} <> env, R, k, s, entries, steps, open)
    case IR.Bind{IR.Add{+left, +right}, level, body} o:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      +l = Evm.limit.of(s)
      +sum = Nat.add(a, b)
      add_step(Nat.is_lt(sum, l), Nat.is_eq(Yul.gt(b, Yul.sub(Yul.not(0n, l), a, l), l), 0n), guard(a, b, l), sum, l, R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k, s),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k, s), obs(entries, steps, R, open),
        sim(body, o, IR.Binding{level, Yul.add(a, b, l)} <> env, R, k, s, entries, steps, open))
    case IR.Bind{IR.Sub{+left, +right}, level, body} o:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      +l = Evm.limit.of(s)
      sub_step(Nat.is_lt(a, b), Bool.pick(Nat, Nat.is_lt(b, l), Nat.sub(l, Nat.sub(b, a)), l), Nat.sub(a, b), R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k, s),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k, s), obs(entries, steps, R, open),
        sim(body, o, IR.Binding{level, Yul.sub(a, b, l)} <> env, R, k, s, entries, steps, open))
    case IR.Bind{IR.Mul{+left, +right}, level, body} o:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      +l = Evm.limit.of(s)
      +prod = Nat.mul(a, b)
      mul_step(prod, l, Nat.is_lt(prod, l), Nat.is_eq(mul.check(a, b, l), 0n), mul_guard(a, b, l), {==}, R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k, s),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k, s), obs(entries, steps, R, open),
        sim(body, o, IR.Binding{level, prod} <> env, R, k, s, entries, steps, open))
    case IR.Bind{IR.Div{+left, +right}, level, body} o:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      sub_step(Nat.is_eq(b, 0n), 0n, Nat.div(a, b), R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k, s),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k, s), obs(entries, steps, R, open),
        sim(body, o, IR.Binding{level, Bool.pick(Nat, Nat.is_eq(b, 0n), 0n, Nat.div(a, b))} <> env, R, k, s, entries, steps, open))
    case IR.Bind{IR.Mod{+left, +right}, level, body} o:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      sub_step(Nat.is_eq(b, 0n), 0n, Nat.mod(a, b), R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k, s),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k, s), obs(entries, steps, R, open),
        sim(body, o, IR.Binding{level, Bool.pick(Nat, Nat.is_eq(b, 0n), 0n, Nat.mod(a, b))} <> env, R, k, s, entries, steps, open))
    case IR.Bind{IR.Math{+op, +args}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.op(op, IR.evals(args, env), Evm.limit.of(s))} <> env, R, k, s, entries, steps, open)
    case IR.Bind{IR.Select{+c, +yes, +no}, level, body} o:
      +v = Bool.pick(Nat, IR.cond(c, env), IR.eval(yes, env), IR.eval(no, env))
      %test_bit(c, env, s) : {obs(entries, steps, R, open)(Yul.exec(Yul.lower(body, o), o,
        IR.Binding{level, Bool.pick(Nat, Nat.is_eq(_, 0n), IR.eval(no, env), IR.eval(yes, env))} <> env, R, k, s))
        == obs(entries, steps, R, open)(IR.run(body, o, IR.Binding{level, v} <> env, R, k, s)) : Evm.Outcome<R>}
      %select_eq(IR.cond(c, env), IR.eval(yes, env), IR.eval(no, env)) : {obs(entries, steps, R, open)(Yul.exec(Yul.lower(body, o), o, IR.Binding{level, _} <> env, R, k, s))
        == obs(entries, steps, R, open)(IR.run(body, o, IR.Binding{level, v} <> env, R, k, s)) : Evm.Outcome<R>}
      sim(body, o, IR.Binding{level, v} <> env, R, k, s, entries, steps, open)
    case IR.Bind{IR.Max{}, level, body} o:
      +l = Evm.limit.of(s)
      %max_eq(l) : {obs(entries, steps, R, open)(Yul.exec(Yul.lower(body, o), o, IR.Binding{level, _} <> env, R, k, s))
        == obs(entries, steps, R, open)(IR.run(body, o, IR.Binding{level, Nat.sub(l, 1n)} <> env, R, k, s)) : Evm.Outcome<R>}
      sim(body, o, IR.Binding{level, Nat.sub(l, 1n)} <> env, R, k, s, entries, steps, open)
    case IR.Bind{IR.Env{+e, args}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.sense(e, IR.evals(args, env), s)} <> env, R, k, Evm.sensed(e, s), entries, steps, open)
    case IR.Bind{IR.Self{}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.self.of(Evm.world.of(s))} <> env, R, k, s, entries, steps, open)
    case IR.Bind{IR.Keccak{words}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.hash.of(Evm.hashes.of(Evm.world.of(s)), Evm.Words{IR.evals(words, env)})} <> env, R, k, s, entries, steps, open)
    case IR.Bind{IR.Typed{d, m}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.hash.of(Evm.hashes.of(Evm.world.of(s)), Evm.Typed{IR.eval(d, env), IR.eval(m, env)})} <> env, R, k, s, entries, steps, open)
    case IR.Bind{IR.Id{t}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.hash.of(Evm.hashes.of(Evm.world.of(s)), Evm.Text{t})} <> env, R, k, s, entries, steps, open)
    case IR.Bind{IR.Recover{d, v, r, g}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.signer.of(Evm.signers.of(Evm.world.of(s)), IR.eval(d, env), IR.eval(v, env), IR.eval(r, env), IR.eval(g, env))} <> env, R, k, s, entries, steps, open)
    case IR.Bind{IR.View{t, g, args}, level, body} o:
      view_step(Evm.Call{IR.eval(t, env), IR.name(g), IR.evals(args, env)}, R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k),
        s, obs(entries, steps, R, open), x => u => sim(body, o, IR.Binding{level, x} <> env, R, k, u, entries, steps, open))
    case IR.Bind{IR.Call{t, g, args}, level, body} o:
      call_step(Evm.Call{IR.eval(t, env), IR.name(g), IR.evals(args, env)}, R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k),
        s, entries, steps, open, rest => x => u => sim(body, o, IR.Binding{level, x} <> env, R, k, u, entries, rest, False{}))
    case IR.Then{IR.SStore{loc, value}, body} o:
      sim(body, o, env, R, k, Evm.write.go(IR.loc(loc, env), IR.eval(value, env), s), entries, steps, open)
    case IR.Then{IR.Log{event, topics, data}, body} o:
      sim(body, o, env, R, k, Evm.log.go(IR.name(event), IR.evals(topics, env), IR.evals(data, env), s), entries, steps, open)
    case IR.Then{IR.Require{+c}, body} o:
      %test_bit(c, env, s) : {obs(entries, steps, R, open)(Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(Nat.is_eq(_, 0n)), 0n), Yul.exec(Yul.lower(body, o), o, env, R, k, s),
        Evm.Revert{})) == obs(entries, steps, R, open)(Bool.pick(Evm.Outcome<R>, IR.cond(c, env), IR.run(body, o, env, R, k, s), Evm.Revert{})) : Evm.Outcome<R>}
      require_step(IR.cond(c, env), R, Evm.Revert{}, Yul.exec(Yul.lower(body, o), o, env, R, k, s),
        IR.run(body, o, env, R, k, s), obs(entries, steps, R, open), sim(body, o, env, R, k, s, entries, steps, open))
    case IR.Then{IR.Ensure{+c, +error, +args}, body} o:
      +e : Evm.Error = Evm.Error{IR.name(error), IR.evals(args, env)}
      %test_bit(c, env, s) : {obs(entries, steps, R, open)(Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(Nat.is_eq(_, 0n)), 0n), Yul.exec(Yul.lower(body, o), o, env, R, k, s),
        Evm.Raise{e})) == obs(entries, steps, R, open)(Bool.pick(Evm.Outcome<R>, IR.cond(c, env), IR.run(body, o, env, R, k, s), Evm.Raise{e})) : Evm.Outcome<R>}
      require_step(IR.cond(c, env), R, Evm.Raise{e}, Yul.exec(Yul.lower(body, o), o, env, R, k, s), IR.run(body, o, env, R, k, s), obs(entries, steps, R, open),
        sim(body, o, env, R, k, s, entries, steps, open))
    case IR.Then{IR.Pay{t, a}, body} o:
      call_step(Evm.Pay{IR.eval(t, env), IR.eval(a, env)}, R,
        _ => Yul.exec(Yul.lower(body, o), o, env, R, k),
        _ => IR.run(body, o, env, R, k),
        s, entries, steps, open, rest => _ => u => sim(body, o, env, R, k, u, entries, rest, False{}))
    case IR.Return{_} IR.Returns{}:
      {==}
    case IR.Return{_} IR.Stops{}:
      {==}
    case IR.Tail{IR.SLoad{_}} IR.Returns{}:
      {==}
    case IR.Tail{IR.Caller{}} IR.Returns{}:
      {==}
    case IR.Tail{IR.Add{+left, +right}} IR.Returns{}:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      +l = Evm.limit.of(s)
      +sum = Nat.add(a, b)
      add_step(Nat.is_lt(sum, l), Nat.is_eq(Yul.gt(b, Yul.sub(Yul.not(0n, l), a, l), l), 0n), guard(a, b, l), sum, l, R,
        x => k(x, s), x => k(x, s), obs(entries, steps, R, open), {==})
    case IR.Tail{IR.Sub{+left, +right}} IR.Returns{}:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      +l = Evm.limit.of(s)
      sub_step(Nat.is_lt(a, b), Bool.pick(Nat, Nat.is_lt(b, l), Nat.sub(l, Nat.sub(b, a)), l), Nat.sub(a, b), R,
        x => k(x, s), x => k(x, s), obs(entries, steps, R, open), {==})
    case IR.Tail{IR.Mul{+left, +right}} IR.Returns{}:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      +l = Evm.limit.of(s)
      mul_step(Nat.mul(a, b), l, Nat.is_lt(Nat.mul(a, b), l), Nat.is_eq(mul.check(a, b, l), 0n), mul_guard(a, b, l), {==}, R,
        x => k(x, s), x => k(x, s), obs(entries, steps, R, open), {==})
    case IR.Tail{IR.Div{+left, +right}} IR.Returns{}:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      sub_step(Nat.is_eq(b, 0n), 0n, Nat.div(a, b), R, x => k(x, s), x => k(x, s), obs(entries, steps, R, open), {==})
    case IR.Tail{IR.Mod{+left, +right}} IR.Returns{}:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      sub_step(Nat.is_eq(b, 0n), 0n, Nat.mod(a, b), R, x => k(x, s), x => k(x, s), obs(entries, steps, R, open), {==})
    case IR.Tail{IR.Math{_, _}} IR.Returns{}:
      {==}
    case IR.Tail{IR.Select{+c, +yes, +no}} IR.Returns{}:
      %test_bit(c, env, s) : {obs(entries, steps, R, open)(k(Bool.pick(Nat, Nat.is_eq(_, 0n), IR.eval(no, env), IR.eval(yes, env)), s))
        == obs(entries, steps, R, open)(k(Bool.pick(Nat, IR.cond(c, env), IR.eval(yes, env), IR.eval(no, env)), s)) : Evm.Outcome<R>}
      %select_eq(IR.cond(c, env), IR.eval(yes, env), IR.eval(no, env)) : {obs(entries, steps, R, open)(k(_, s))
        == obs(entries, steps, R, open)(k(Bool.pick(Nat, IR.cond(c, env), IR.eval(yes, env), IR.eval(no, env)), s)) : Evm.Outcome<R>}
      {==}
    case IR.Tail{IR.Max{}} IR.Returns{}:
      %max_eq(Evm.limit.of(s)) : {obs(entries, steps, R, open)(k(_, s)) == obs(entries, steps, R, open)(k(Nat.sub(Evm.limit.of(s), 1n), s)) : Evm.Outcome<R>}
      {==}
    case IR.Tail{IR.Env{_, _}} IR.Returns{}:
      {==}
    case IR.Tail{IR.Self{}} IR.Returns{}:
      {==}
    case IR.Tail{IR.Keccak{_}} IR.Returns{}:
      {==}
    case IR.Tail{IR.Typed{_, _}} IR.Returns{}:
      {==}
    case IR.Tail{IR.Id{_}} IR.Returns{}:
      {==}
    case IR.Tail{IR.Recover{_, _, _, _}} IR.Returns{}:
      {==}
    case IR.Tail{IR.View{_, _, _}} IR.Returns{}:
      {==}
    case IR.Tail{IR.Call{_, _, _}} IR.Returns{}:
      {==}
    case IR.Tail{IR.SLoad{_}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Caller{}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Add{_, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Sub{_, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Mul{_, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Div{_, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Mod{_, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Math{_, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Select{_, _, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Max{}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Env{_, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Self{}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Keccak{_}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Typed{_, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Id{_}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Recover{_, _, _, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.View{_, _, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Call{_, _, _}} IR.Stops{}:
      {==}
    case IR.Finish{IR.SStore{_, _}} IR.Stops{}:
      {==}
    case IR.Finish{IR.Log{_, _, _}} IR.Stops{}:
      {==}
    case IR.Finish{IR.Require{+c}} IR.Stops{}:
      %test_bit(c, env, s) : {obs(entries, steps, R, open)(Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(Nat.is_eq(_, 0n)), 0n), k(Unit{}, s), Evm.Revert{}))
        == obs(entries, steps, R, open)(Bool.pick(Evm.Outcome<R>, IR.cond(c, env), k(Unit{}, s), Evm.Revert{})) : Evm.Outcome<R>}
      require_step(IR.cond(c, env), R, Evm.Revert{}, k(Unit{}, s), k(Unit{}, s), obs(entries, steps, R, open), {==})
    case IR.Finish{IR.Ensure{+c, +error, +args}} IR.Stops{}:
      +e : Evm.Error = Evm.Error{IR.name(error), IR.evals(args, env)}
      %test_bit(c, env, s) : {obs(entries, steps, R, open)(Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(Nat.is_eq(_, 0n)), 0n), k(Unit{}, s), Evm.Raise{e}))
        == obs(entries, steps, R, open)(Bool.pick(Evm.Outcome<R>, IR.cond(c, env), k(Unit{}, s), Evm.Raise{e})) : Evm.Outcome<R>}
      require_step(IR.cond(c, env), R, Evm.Raise{e}, k(Unit{}, s), k(Unit{}, s), obs(entries, steps, R, open), {==})
    case IR.Finish{IR.SStore{_, _}} IR.Returns{}:
      {==}
    case IR.Finish{IR.Log{_, _, _}} IR.Returns{}:
      {==}
    case IR.Finish{IR.Require{_}} IR.Returns{}:
      {==}
    case IR.Finish{IR.Ensure{_, _, _}} IR.Returns{}:
      {==}
    case IR.Finish{IR.Pay{_, _}} IR.Stops{}:
      {==}
    case IR.Finish{IR.Pay{_, _}} IR.Returns{}:
      {==}
    case IR.Stop{} IR.Stops{}:
      {==}
    case IR.Stop{} IR.Returns{}:
      {==}
    case IR.If{+c, yes, no} o:
      if_step(IR.cond(c, env), Yul.eval(Yul.lower.test(c), env, s), test_bit(c, env, s), IR.value(o), R,
        Yul.exec(Yul.lower(yes, o), o, env), Yul.exec(Yul.lower(no, o), o, env), IR.run(yes, o, env), IR.run(no, o, env),
        k, s, obs(entries, steps, R, open), sim(yes, o, env, R, k, s, entries, steps, open), sim(no, o, env, R, k, s, entries, steps, open))

# A callback: an entry's Yul lowering and its IR agree under any answers.
# Both check that the entry's IR is closed first.
def closed_step(b: Bool, -A: Data, -y: Evm.Contract(A), -f: Evm.Contract(A), -z: Evm.Contract(A),
  -k: A -> Evm.State -> Evm.Outcome<Unit>, +s: Evm.State, -d: Evm.Outcome<Unit> -> Evm.Outcome<Unit>,
  h: {d(y(Unit, k, s)) == d(f(Unit, k, s)) : Evm.Outcome<Unit>}) ->
  {d(Bool.pick(Evm.Contract(A), b, y, z, Unit, k, s)) == d(Bool.pick(Evm.Contract(A), b, f, z, Unit, k, s)) : Evm.Outcome<Unit>}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def started_step(+cmd: IR.Cmd, +out: IR.Output, env: Maybe<&2, List<&2, IR.Binding>>, +entries: List<&2, Calls.Entry>,
  +inner: List<&2, Calls.Step>, -k: Unit -> Evm.State -> Evm.Outcome<Unit>, +s: Evm.State) ->
  {Calls.drive(Calls.Model{}, entries, inner, Unit, False{}, Calls.started(Calls.Lowered{}, cmd, out, env, Unit, k, s))
    == Calls.drive(Calls.Model{}, entries, inner, Unit, False{}, Calls.started(Calls.Model{}, cmd, out, env, Unit, k, s)) : Evm.Outcome<Unit>}:
  match env:
    case None{}:
      {==}
    case Some{+bs}:
      closed_step(IR.closed(cmd, IR.levels(bs)), IR.value(out), Yul.exec(Yul.lower(cmd, out), out, bs), IR.run(cmd, out, bs),
        IR.abort(IR.value(out)), x => Evm.Contract.pure(Unit, Unit{}, Unit, k), s, obs(entries, inner, Unit, False{}),
        sim(cmd, out, bs, Unit, x => Evm.Contract.pure(Unit, Unit{}, Unit, k), s, entries, inner, False{}))

def found_step(e: Maybe<&2, Calls.Entry>, args: List<&2, Nat>, +entries: List<&2, Calls.Entry>,
  +inner: List<&2, Calls.Step>, -k: Unit -> Evm.State -> Evm.Outcome<Unit>, +s: Evm.State) ->
  {Calls.drive(Calls.Model{}, entries, inner, Unit, False{}, Calls.found(Calls.Lowered{}, e, args, Unit, k, s))
    == Calls.drive(Calls.Model{}, entries, inner, Unit, False{}, Calls.found(Calls.Model{}, e, args, Unit, k, s)) : Evm.Outcome<Unit>}:
  match e:
    case None{}:
      {==}
    case Some{Calls.Entry{+cmd, +out, arity}}:
      started_step(cmd, out, Calls.bind(arity, 0n, args), entries, inner, k, s)

# Induction on the answers: callbacks into the lowered entries and into
# their IR give the same outcome.
def table(+entries: List<&2, Calls.Entry>, steps: List<&2, Calls.Step>, -A: Data, +open: Bool, o: Evm.Outcome<A>) ->
  {Calls.drive(Calls.Lowered{}, entries, steps, A, open, o) == Calls.drive(Calls.Model{}, entries, steps, A, open, o) : Evm.Outcome<A>}:
  match steps:
    case Nil{}:
      {==}
    case step <> +rest:
      match step:
        case Calls.Enter{+sender, +i, +args, +inner}:
          match open:
            case True{}:
              match o:
                case Evm.Ok{+v, +s}:
                  +w : Evm.State = Calls.with.caller(sender, s)
                  %found_step(Calls.entry(entries, i), args, entries, inner, u => t => Evm.Ok{u, t}, w) :
                    {Calls.drive(Calls.Lowered{}, entries, rest, A, True{}, Evm.Ok{v, Calls.back(Unit, s, Calls.drive(Calls.Lowered{}, entries, inner, Unit, False{},
                      Calls.callback(Calls.Lowered{}, entries, i, args, Unit, u => t => Evm.Ok{u, t}, w)))})
                    == Calls.drive(Calls.Model{}, entries, rest, A, True{}, Evm.Ok{v, Calls.back(Unit, s, _)}) : Evm.Outcome<A>}
                  %table(entries, inner, Unit, False{}, Calls.callback(Calls.Lowered{}, entries, i, args, Unit, u => t => Evm.Ok{u, t}, w)) :
                    {Calls.drive(Calls.Lowered{}, entries, rest, A, True{}, Evm.Ok{v, Calls.back(Unit, s, Calls.drive(Calls.Lowered{}, entries, inner, Unit, False{},
                      Calls.callback(Calls.Lowered{}, entries, i, args, Unit, u => t => Evm.Ok{u, t}, w)))})
                    == Calls.drive(Calls.Model{}, entries, rest, A, True{}, Evm.Ok{v, Calls.back(Unit, s, _)}) : Evm.Outcome<A>}
                  table(entries, rest, A, True{}, Evm.Ok{v, Calls.back(Unit, s, Calls.drive(Calls.Lowered{}, entries, inner, Unit, False{},
                    Calls.callback(Calls.Lowered{}, entries, i, args, Unit, u => t => Evm.Ok{u, t}, w)))})
                case Evm.Revert{}:
                  {==}
                case Evm.Raise{_}:
                  {==}
                case Evm.Calling{_, _, _}:
                  {==}
            case False{}:
              {==}
        case Calls.Answer{+q, +cbs, +x}:
          match open:
            case True{}:
              {==}
            case False{}:
              match o:
                case Evm.Ok{_, _}:
                  {==}
                case Evm.Revert{}:
                  {==}
                case Evm.Raise{_}:
                  {==}
                case Evm.Calling{+c, +s, r}:
                  +t : Evm.State = Calls.after(Unit, s, Calls.drive(Calls.Lowered{}, entries, cbs, Unit, True{}, Evm.Ok{Unit{}, s}))
                  %table(entries, cbs, Unit, True{}, Evm.Ok{Unit{}, s}) :
                    {Bool.pick(Evm.Outcome<A>, Evm.same.call(q, c), Calls.drive(Calls.Lowered{}, entries, rest, A, False{}, r(x, t)), Evm.Revert{})
                    == Bool.pick(Evm.Outcome<A>, Evm.same.call(q, c), Calls.drive(Calls.Model{}, entries, rest, A, False{},
                      r(x, Calls.after(Unit, s, _))), Evm.Revert{}) : Evm.Outcome<A>}
                  %table(entries, rest, A, False{}, r(x, t)) :
                    {Bool.pick(Evm.Outcome<A>, Evm.same.call(q, c), Calls.drive(Calls.Lowered{}, entries, rest, A, False{}, r(x, t)), Evm.Revert{})
                    == Bool.pick(Evm.Outcome<A>, Evm.same.call(q, c), _, Evm.Revert{}) : Evm.Outcome<A>}
                  {==}

def Laws.preserves(entries, steps, cmd, out, env, R, k, s, open):
  Equal.trans(Evm.Outcome<R>,
    Calls.drive(Calls.Lowered{}, entries, steps, R, open, Yul.exec(Yul.lower(cmd, out), out, env, R, k, s)),
    Calls.drive(Calls.Model{}, entries, steps, R, open, Yul.exec(Yul.lower(cmd, out), out, env, R, k, s)),
    Calls.drive(Calls.Model{}, entries, steps, R, open, IR.run(cmd, out, env, R, k, s)),
    table(entries, steps, R, open, Yul.exec(Yul.lower(cmd, out), out, env, R, k, s)),
    sim(cmd, out, env, R, k, s, entries, steps, open))

def Laws.callbacks(entries, steps, A, open, o):
  table(entries, steps, A, open, o)

def Laws.fixed(e, s, h):
  %h : {Bool.pick(Evm.State, _, s, Evm.used(s)) == s : Evm.State}
  {==}
