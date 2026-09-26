import Base
import ./Evm.bend as Evm
import ./ir.bend as IR
import ./yul.bend as Yul
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

# Checked add: the guard passes exactly when Evm.add does, and then wrapping
# add is the plain sum. y and f are the rest of the Yul and IR runs.
def add_step(c: Bool, v: Bool, g: {c == v : Bool}, +sum: Nat, +l: Nat, -R: Data,
  -y: Nat -> Evm.Outcome<R>, -f: Nat -> Evm.Outcome<R>,
  h: {y(Bool.pick(Nat, c, sum, Nat.sub(sum, l))) == f(Bool.pick(Nat, c, sum, Nat.sub(sum, l))) : Evm.Outcome<R>}) ->
  {Bool.pick(Evm.Outcome<R>, v, y(Bool.pick(Nat, c, sum, Nat.sub(sum, l))), Evm.Revert{})
    == Bool.pick(Evm.Outcome<R>, c, f(sum), Evm.Revert{}) : Evm.Outcome<R>}:
  match c:
    case True{}:
      %g : {Bool.pick(Evm.Outcome<R>, _, y(sum), Evm.Revert{}) == f(sum) : Evm.Outcome<R>}
      h
    case False{}:
      %g : {Bool.pick(Evm.Outcome<R>, _, y(Nat.sub(sum, l)), Evm.Revert{}) == Evm.Revert{} : Evm.Outcome<R>}
      {==}

# Checked sub: `if lt(a, b)` reverts exactly when Evm.sub does, and when it
# passes, Yul.sub is a - b.
def sub_step(c: Bool, -x: Nat, +d: Nat, -R: Data, -y: Nat -> Evm.Outcome<R>, -f: Nat -> Evm.Outcome<R>,
  h: {y(Bool.pick(Nat, c, x, d)) == f(Bool.pick(Nat, c, x, d)) : Evm.Outcome<R>}) ->
  {Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(c), 0n), y(Bool.pick(Nat, c, x, d)), Evm.Revert{})
    == Bool.pick(Evm.Outcome<R>, c, Evm.Revert{}, f(d)) : Evm.Outcome<R>}:
  match c:
    case True{}:
      {==}
    case False{}:
      h

# A Require or an Ensure: iszero(cond) fails with x exactly when the
# condition is false.
def require_step(c: Bool, -R: Data, -x: Evm.Outcome<R>, -y: Evm.Outcome<R>, -f: Evm.Outcome<R>, h: {y == f : Evm.Outcome<R>}) ->
  {Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(Nat.is_eq(Yul.bit(c), 0n)), 0n), y, x)
    == Bool.pick(Evm.Outcome<R>, c, f, x) : Evm.Outcome<R>}:
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
  ha: {ya(R, k, s) == ia(R, k, s) : Evm.Outcome<R>}, hb: {yb(R, k, s) == ib(R, k, s) : Evm.Outcome<R>}) ->
  {Evm.branch(A, Nat.is_eq(n, 0n), yb, ya, R, k, s) == Evm.branch(A, c, ia, ib, R, k, s) : Evm.Outcome<R>}:
  match c:
    case True{}:
      %e : {Evm.branch(A, Nat.is_eq(_, 0n), yb, ya, R, k, s) == ia(R, k, s) : Evm.Outcome<R>}
      ha
    case False{}:
      %e : {Evm.branch(A, Nat.is_eq(_, 0n), yb, ya, R, k, s) == ib(R, k, s) : Evm.Outcome<R>}
      hb

# A View: Yul and the IR make the same call, and their continuations agree
# on every answer and state, so the outcomes agree.
def view_step(+c: Evm.Call, -R: Data, -y: Nat -> Evm.State -> Evm.Outcome<R>, -f: Nat -> Evm.State -> Evm.Outcome<R>,
  +s: Evm.State, h: @x: Nat -> @t: Evm.State -> {y(x, t) == f(x, t) : Evm.Outcome<R>}) ->
  {Evm.answer(R, c, y, s) == Evm.answer(R, c, f, s) : Evm.Outcome<R>}:
  match s:
    case Evm.State{storage, caller, limit, logs, Evm.World{time, chain, self, hashes, signers, answers}}:
      match answers:
        case Nil{}:
          {==}
        case Evm.Answer{q, x} <> rest:
          +t : Evm.State = Evm.State{storage, caller, limit, logs, Evm.World{time, chain, self, hashes, signers, rest}}
          %h(x, t) : {Bool.pick(Evm.Outcome<R>, Evm.same.call(q, c), y(x, t), Evm.Revert{})
            == Bool.pick(Evm.Outcome<R>, Evm.same.call(q, c), _, Evm.Revert{}) : Evm.Outcome<R>}
          {==}

# Induction on the command. Both runs pass the same state and continuation on,
# so only the checks and ifs need lemmas. The continuation is erased, so an
# If's two arms can both use it.
def sim(+cmd: IR.Cmd, +out: IR.Output, +env: List<&2, IR.Binding>, -R: Data,
  -k: IR.value(out) -> Evm.State -> Evm.Outcome<R>, +s: Evm.State) ->
  {Yul.exec(Yul.lower(cmd, out), out, env, R, k, s) == IR.run(cmd, out, env, R, k, s) : Evm.Outcome<R>}:
  match cmd out:
    case IR.Bind{IR.SLoad{loc}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.lookup(Evm.storage.of(s), IR.loc(loc, env))} <> env, R, k, s)
    case IR.Bind{IR.Caller{}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.caller.of(s)} <> env, R, k, s)
    case IR.Bind{IR.Add{+left, +right}, level, body} o:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      +l = Evm.limit.of(s)
      +sum = Nat.add(a, b)
      add_step(Nat.is_lt(sum, l), Nat.is_eq(Yul.gt(b, Yul.sub(Yul.not(0n, l), a, l), l), 0n), guard(a, b, l), sum, l, R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k, s),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k, s),
        sim(body, o, IR.Binding{level, Yul.add(a, b, l)} <> env, R, k, s))
    case IR.Bind{IR.Sub{+left, +right}, level, body} o:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      +l = Evm.limit.of(s)
      sub_step(Nat.is_lt(a, b), Bool.pick(Nat, Nat.is_lt(b, l), Nat.sub(l, Nat.sub(b, a)), l), Nat.sub(a, b), R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k, s),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k, s),
        sim(body, o, IR.Binding{level, Yul.sub(a, b, l)} <> env, R, k, s))
    case IR.Bind{IR.Select{+c, +yes, +no}, level, body} o:
      +v = Bool.pick(Nat, IR.cond(c, env), IR.eval(yes, env), IR.eval(no, env))
      %test_bit(c, env, s) : {Yul.exec(Yul.lower(body, o), o,
        IR.Binding{level, Bool.pick(Nat, Nat.is_eq(_, 0n), IR.eval(no, env), IR.eval(yes, env))} <> env, R, k, s)
        == IR.run(body, o, IR.Binding{level, v} <> env, R, k, s) : Evm.Outcome<R>}
      %select_eq(IR.cond(c, env), IR.eval(yes, env), IR.eval(no, env)) : {Yul.exec(Yul.lower(body, o), o, IR.Binding{level, _} <> env, R, k, s)
        == IR.run(body, o, IR.Binding{level, v} <> env, R, k, s) : Evm.Outcome<R>}
      sim(body, o, IR.Binding{level, v} <> env, R, k, s)
    case IR.Bind{IR.Max{}, level, body} o:
      +l = Evm.limit.of(s)
      %max_eq(l) : {Yul.exec(Yul.lower(body, o), o, IR.Binding{level, _} <> env, R, k, s)
        == IR.run(body, o, IR.Binding{level, Nat.sub(l, 1n)} <> env, R, k, s) : Evm.Outcome<R>}
      sim(body, o, IR.Binding{level, Nat.sub(l, 1n)} <> env, R, k, s)
    case IR.Bind{IR.Timestamp{}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.time.of(Evm.world.of(s))} <> env, R, k, s)
    case IR.Bind{IR.ChainId{}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.chain.of(Evm.world.of(s))} <> env, R, k, s)
    case IR.Bind{IR.Self{}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.self.of(Evm.world.of(s))} <> env, R, k, s)
    case IR.Bind{IR.Keccak{words}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.hash.of(Evm.hashes.of(Evm.world.of(s)), Evm.Words{IR.evals(words, env)})} <> env, R, k, s)
    case IR.Bind{IR.Typed{d, m}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.hash.of(Evm.hashes.of(Evm.world.of(s)), Evm.Typed{IR.eval(d, env), IR.eval(m, env)})} <> env, R, k, s)
    case IR.Bind{IR.Id{t}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.hash.of(Evm.hashes.of(Evm.world.of(s)), Evm.Text{t})} <> env, R, k, s)
    case IR.Bind{IR.Recover{d, v, r, g}, level, body} o:
      sim(body, o, IR.Binding{level, Evm.signer.of(Evm.signers.of(Evm.world.of(s)), IR.eval(d, env), IR.eval(v, env), IR.eval(r, env), IR.eval(g, env))} <> env, R, k, s)
    case IR.Bind{IR.View{t, g, args}, level, body} o:
      view_step(Evm.Call{IR.eval(t, env), IR.name(g), IR.evals(args, env)}, R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k),
        s, x => u => sim(body, o, IR.Binding{level, x} <> env, R, k, u))
    case IR.Then{IR.SStore{loc, value}, body} o:
      sim(body, o, env, R, k, Evm.write.go(IR.loc(loc, env), IR.eval(value, env), s))
    case IR.Then{IR.Log{event, topics, data}, body} o:
      sim(body, o, env, R, k, Evm.log.go(IR.name(event), IR.evals(topics, env), IR.evals(data, env), s))
    case IR.Then{IR.Require{+c}, body} o:
      %test_bit(c, env, s) : {Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(Nat.is_eq(_, 0n)), 0n), Yul.exec(Yul.lower(body, o), o, env, R, k, s),
        Evm.Revert{}) == Bool.pick(Evm.Outcome<R>, IR.cond(c, env), IR.run(body, o, env, R, k, s), Evm.Revert{}) : Evm.Outcome<R>}
      require_step(IR.cond(c, env), R, Evm.Revert{}, Yul.exec(Yul.lower(body, o), o, env, R, k, s),
        IR.run(body, o, env, R, k, s), sim(body, o, env, R, k, s))
    case IR.Then{IR.Ensure{+c, +error, +args}, body} o:
      +x : Evm.Outcome<R> = Evm.Raise{Evm.Error{IR.name(error), IR.evals(args, env)}}
      %test_bit(c, env, s) : {Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(Nat.is_eq(_, 0n)), 0n), Yul.exec(Yul.lower(body, o), o, env, R, k, s),
        x) == Bool.pick(Evm.Outcome<R>, IR.cond(c, env), IR.run(body, o, env, R, k, s), x) : Evm.Outcome<R>}
      require_step(IR.cond(c, env), R, x, Yul.exec(Yul.lower(body, o), o, env, R, k, s), IR.run(body, o, env, R, k, s),
        sim(body, o, env, R, k, s))
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
        x => k(x, s), x => k(x, s), {==})
    case IR.Tail{IR.Sub{+left, +right}} IR.Returns{}:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      +l = Evm.limit.of(s)
      sub_step(Nat.is_lt(a, b), Bool.pick(Nat, Nat.is_lt(b, l), Nat.sub(l, Nat.sub(b, a)), l), Nat.sub(a, b), R,
        x => k(x, s), x => k(x, s), {==})
    case IR.Tail{IR.Select{+c, +yes, +no}} IR.Returns{}:
      %test_bit(c, env, s) : {k(Bool.pick(Nat, Nat.is_eq(_, 0n), IR.eval(no, env), IR.eval(yes, env)), s)
        == k(Bool.pick(Nat, IR.cond(c, env), IR.eval(yes, env), IR.eval(no, env)), s) : Evm.Outcome<R>}
      %select_eq(IR.cond(c, env), IR.eval(yes, env), IR.eval(no, env)) : {k(_, s)
        == k(Bool.pick(Nat, IR.cond(c, env), IR.eval(yes, env), IR.eval(no, env)), s) : Evm.Outcome<R>}
      {==}
    case IR.Tail{IR.Max{}} IR.Returns{}:
      %max_eq(Evm.limit.of(s)) : {k(_, s) == k(Nat.sub(Evm.limit.of(s), 1n), s) : Evm.Outcome<R>}
      {==}
    case IR.Tail{IR.Timestamp{}} IR.Returns{}:
      {==}
    case IR.Tail{IR.ChainId{}} IR.Returns{}:
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
    case IR.Tail{IR.SLoad{_}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Caller{}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Add{_, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Sub{_, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Select{_, _, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Max{}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Timestamp{}} IR.Stops{}:
      {==}
    case IR.Tail{IR.ChainId{}} IR.Stops{}:
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
    case IR.Finish{IR.SStore{_, _}} IR.Stops{}:
      {==}
    case IR.Finish{IR.Log{_, _, _}} IR.Stops{}:
      {==}
    case IR.Finish{IR.Require{+c}} IR.Stops{}:
      %test_bit(c, env, s) : {Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(Nat.is_eq(_, 0n)), 0n), k(Unit{}, s), Evm.Revert{})
        == Bool.pick(Evm.Outcome<R>, IR.cond(c, env), k(Unit{}, s), Evm.Revert{}) : Evm.Outcome<R>}
      require_step(IR.cond(c, env), R, Evm.Revert{}, k(Unit{}, s), k(Unit{}, s), {==})
    case IR.Finish{IR.Ensure{+c, +error, +args}} IR.Stops{}:
      +x : Evm.Outcome<R> = Evm.Raise{Evm.Error{IR.name(error), IR.evals(args, env)}}
      %test_bit(c, env, s) : {Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(Nat.is_eq(_, 0n)), 0n), k(Unit{}, s), x)
        == Bool.pick(Evm.Outcome<R>, IR.cond(c, env), k(Unit{}, s), x) : Evm.Outcome<R>}
      require_step(IR.cond(c, env), R, x, k(Unit{}, s), k(Unit{}, s), {==})
    case IR.Finish{IR.SStore{_, _}} IR.Returns{}:
      {==}
    case IR.Finish{IR.Log{_, _, _}} IR.Returns{}:
      {==}
    case IR.Finish{IR.Require{_}} IR.Returns{}:
      {==}
    case IR.Finish{IR.Ensure{_, _, _}} IR.Returns{}:
      {==}
    case IR.Stop{} IR.Stops{}:
      {==}
    case IR.Stop{} IR.Returns{}:
      {==}
    case IR.If{+c, yes, no} o:
      if_step(IR.cond(c, env), Yul.eval(Yul.lower.test(c), env, s), test_bit(c, env, s), IR.value(o), R,
        Yul.exec(Yul.lower(yes, o), o, env), Yul.exec(Yul.lower(no, o), o, env), IR.run(yes, o, env), IR.run(no, o, env),
        k, s, sim(yes, o, env, R, k, s), sim(no, o, env, R, k, s))

def Laws.preserves(cmd, out, env, R, k, s):
  sim(cmd, out, env, R, k, s)
