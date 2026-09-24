import Base
import ./Evm.bend as Evm
import ./ir.bend as IR
import ./yul.bend as Yul
import ./LAWS.bend as Laws

# Nat facts for the overflow check. Each is proved by induction.

def disc(+b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def never(+e: {True{} == False{} : Bool}) -> Empty:
  %e : disc(_)
  Unit{}

def absurd(-A: Type, +e: {True{} == False{} : Bool}) -> A:
  Empty.absurd(A, never(e))

def lt_zero(+n: Nat) -> {False{} == Nat.is_lt(n, 0n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+_:
      {==}

def lt_succ(+n: Nat) -> {True{} == Nat.is_lt(n, 1n+n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      lt_succ(p)

def lt_irrefl(+n: Nat) -> {False{} == Nat.is_lt(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      lt_irrefl(p)

def sub_zero(+n: Nat) -> {n == Nat.sub(n, 0n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+_:
      {==}

def lt_step(+x: Nat, +n: Nat, +e: {True{} == Nat.is_lt(x, n) : Bool}) -> {True{} == Nat.is_lt(x, 1n+n) : Bool}:
  match x n:
    case 0n _:
      {==}
    case 1n+(+y) 0n:
      absurd({True{} == Nat.is_lt(1n+y, 1n) : Bool}, e)
    case 1n+(+y) 1n+(+m):
      lt_step(y, m, e)

def sub_lt_succ(+p: Nat, +a: Nat) -> {True{} == Nat.is_lt(Nat.sub(p, a), 1n+p) : Bool}:
  match p a:
    case 0n 0n:
      {==}
    case 0n 1n+_:
      {==}
    case 1n+(+q) 0n:
      lt_succ(1n+q)
    case 1n+(+q) 1n+(+b):
      lt_step(Nat.sub(q, b), 1n+q, sub_lt_succ(q, b))

# a < c + 1 and c < 0 cannot both hold.
def lt_one(+c: Nat, +e: {True{} == Nat.is_lt(c, 0n) : Bool}) -> {True{} == False{} : Bool}:
  Equal.trans(Bool, True{}, Nat.is_lt(c, 0n), False{}, e, Equal.sym(Bool, False{}, Nat.is_lt(c, 0n), lt_zero(c)))

# a <= p, so p < a is false.
def flip(+a: Nat, +p: Nat, +e: {True{} == Nat.is_lt(a, 1n+p) : Bool}) -> {False{} == Nat.is_lt(p, a) : Bool}:
  match a p:
    case 0n +q:
      lt_zero(q)
    case 1n+(+c) 0n:
      absurd({False{} == Nat.is_lt(0n, 1n+c) : Bool}, lt_one(c, e))
    case 1n+(+c) 1n+(+q):
      flip(c, q, e)

def lt_flip(+p: Nat, +b: Nat) -> {Bool.not(Nat.is_lt(b, 1n+p)) == Nat.is_lt(p, b) : Bool}:
  match p b:
    case 0n 0n:
      {==}
    case 0n 1n+(+c):
      %lt_zero(c) : {Bool.not(_) == True{} : Bool}
      {==}
    case 1n+_ 0n:
      {==}
    case 1n+(+q) 1n+(+c):
      lt_flip(q, c)

# The heart of the check: for a <= p, p - a < b exactly when a + b >= p + 1.
def key(+a: Nat, +p: Nat, +b: Nat, +e: {True{} == Nat.is_lt(a, 1n+p) : Bool}) ->
  {Bool.not(Nat.is_lt(Nat.add(a, b), 1n+p)) == Nat.is_lt(Nat.sub(p, a), b) : Bool}:
  match a p:
    case 0n +q:
      %sub_zero(q) : {Bool.not(Nat.is_lt(b, 1n+q)) == Nat.is_lt(_, b) : Bool}
      lt_flip(q, b)
    case 1n+(+c) 0n:
      absurd({Bool.not(Nat.is_lt(Nat.add(1n+c, b), 1n)) == Nat.is_lt(Nat.sub(0n, 1n+c), b) : Bool}, lt_one(c, e))
    case 1n+(+c) 1n+(+q):
      key(c, q, b, e)

def add_ge(+a: Nat, +b: Nat, +l: Nat, +e: {False{} == Nat.is_lt(a, l) : Bool}) -> {False{} == Nat.is_lt(Nat.add(a, b), l) : Bool}:
  match a l:
    case 0n 0n:
      lt_zero(b)
    case 0n 1n+(+m):
      absurd({False{} == Nat.is_lt(b, 1n+m) : Bool}, Equal.sym(Bool, False{}, True{}, e))
    case 1n+_ 0n:
      {==}
    case 1n+(+c) 1n+(+m):
      add_ge(c, b, m, e)

def bit_not(+c: Bool) -> {c == Nat.is_eq(Yul.bit(Bool.not(c)), 0n) : Bool}:
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

# p < a + 1 fails, so p < a.
def lt_over(+a: Nat, +p: Nat, +e: {False{} == Nat.is_lt(a, 1n+p) : Bool}) -> {True{} == Nat.is_lt(p, a) : Bool}:
  match a p:
    case 0n +q:
      absurd({True{} == Nat.is_lt(q, 0n) : Bool}, Equal.sym(Bool, False{}, True{}, e))
    case 1n+_ 0n:
      {==}
    case 1n+(+c) 1n+(+q):
      lt_over(c, q, e)

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
  %lt_irrefl(l) : {1n == Bool.pick(Nat, _, Yul.bit(Nat.is_lt(l, b)), 1n) : Nat}
  {==}

def guard.succ(+a: Nat, +b: Nat, +p: Nat, +c: Bool, +e: {c == Nat.is_lt(a, 1n+p) : Bool}) ->
  {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(Yul.gt(b, Yul.sub(p, a, 1n+p), 1n+p), 0n) : Bool}:
  match c:
    case True{}:
      %sub_in(p, a, e) : {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(Yul.gt(b, _, 1n+p), 0n) : Bool}
      %gt_in(b, Nat.sub(p, a), 1n+p, sub_lt_succ(p, a)) : {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(_, 0n) : Bool}
      %key(a, p, b, e) : {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(Yul.bit(_), 0n) : Bool}
      bit_not(Nat.is_lt(Nat.add(a, b), 1n+p))
    case False{}:
      %sub_out(p, a, e) : {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(Yul.gt(b, _, 1n+p), 0n) : Bool}
      %gt_out(b, 1n+p) : {Nat.is_lt(Nat.add(a, b), 1n+p) == Nat.is_eq(_, 0n) : Bool}
      %add_ge(a, b, 1n+p, e) : {_ == False{} : Bool}
      {==}

# The overflow check `gt(b, sub(not(0), a))` is zero exactly when a + b < limit.
def guard(+a: Nat, +b: Nat, +l: Nat) -> {Nat.is_lt(Nat.add(a, b), l) == Nat.is_eq(Yul.gt(b, Yul.sub(Yul.not(0n, l), a, l), l), 0n) : Bool}:
  match l:
    case 0n:
      %lt_zero(Yul.sub(Yul.not(0n, 0n), a, 0n)) : {Nat.is_lt(Nat.add(a, b), 0n)
        == Nat.is_eq(Bool.pick(Nat, _, Yul.bit(Nat.is_lt(Yul.sub(Yul.not(0n, 0n), a, 0n), b)), 1n), 0n) : Bool}
      Equal.sym(Bool, False{}, Nat.is_lt(Nat.add(a, b), 0n), lt_zero(Nat.add(a, b)))
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

# A Require: iszero(cond) reverts exactly when the condition is false.
def require_step(c: Bool, -R: Data, -y: Evm.Outcome<R>, -f: Evm.Outcome<R>, h: {y == f : Evm.Outcome<R>}) ->
  {Bool.pick(Evm.Outcome<R>, Nat.is_eq(Yul.bit(Nat.is_eq(Yul.bit(c), 0n)), 0n), y, Evm.Revert{})
    == Bool.pick(Evm.Outcome<R>, c, f, Evm.Revert{}) : Evm.Outcome<R>}:
  match c:
    case True{}:
      h
    case False{}:
      {==}

# Induction on the command. Both runs pass the same state and continuation on,
# so only the checks need lemmas.
def Laws.preserves(cmd, out, env, R, k, s):
  match cmd out:
    case IR.Bind{IR.SLoad{loc}, level, body} o:
      Laws.preserves(body, o, IR.Binding{level, Evm.lookup(Evm.storage.of(s), IR.loc(loc, env))} <> env, R, k, s)
    case IR.Bind{IR.Caller{}, level, body} o:
      Laws.preserves(body, o, IR.Binding{level, Evm.caller.of(s)} <> env, R, k, s)
    case IR.Bind{IR.Add{+left, +right}, level, body} o:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      +l = Evm.limit.of(s)
      +sum = Nat.add(a, b)
      add_step(Nat.is_lt(sum, l), Nat.is_eq(Yul.gt(b, Yul.sub(Yul.not(0n, l), a, l), l), 0n), guard(a, b, l), sum, l, R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k, s),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k, s),
        Laws.preserves(body, o, IR.Binding{level, Yul.add(a, b, l)} <> env, R, k, s))
    case IR.Bind{IR.Sub{+left, +right}, level, body} o:
      +a = IR.eval(left, env)
      +b = IR.eval(right, env)
      +l = Evm.limit.of(s)
      sub_step(Nat.is_lt(a, b), Bool.pick(Nat, Nat.is_lt(b, l), Nat.sub(l, Nat.sub(b, a)), l), Nat.sub(a, b), R,
        x => Yul.exec(Yul.lower(body, o), o, IR.Binding{level, x} <> env, R, k, s),
        x => IR.run(body, o, IR.Binding{level, x} <> env, R, k, s),
        Laws.preserves(body, o, IR.Binding{level, Yul.sub(a, b, l)} <> env, R, k, s))
    case IR.Then{IR.SStore{loc, value}, body} o:
      Laws.preserves(body, o, env, R, k, Evm.write.go(IR.loc(loc, env), IR.eval(value, env), s))
    case IR.Then{IR.Log{event, topics, data}, body} o:
      Laws.preserves(body, o, env, R, k, Evm.log.go(event, IR.evals(topics, env), IR.eval(data, env), s))
    case IR.Then{IR.Require{IR.Eq{left, right}}, body} o:
      require_step(Nat.is_eq(IR.eval(left, env), IR.eval(right, env)), R,
        Yul.exec(Yul.lower(body, o), o, env, R, k, s), IR.run(body, o, env, R, k, s), Laws.preserves(body, o, env, R, k, s))
    case IR.Then{IR.Require{IR.Lt{left, right}}, body} o:
      require_step(Nat.is_lt(IR.eval(left, env), IR.eval(right, env)), R,
        Yul.exec(Yul.lower(body, o), o, env, R, k, s), IR.run(body, o, env, R, k, s), Laws.preserves(body, o, env, R, k, s))
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
    case IR.Tail{IR.SLoad{_}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Caller{}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Add{_, _}} IR.Stops{}:
      {==}
    case IR.Tail{IR.Sub{_, _}} IR.Stops{}:
      {==}
    case IR.Finish{IR.SStore{_, _}} IR.Stops{}:
      {==}
    case IR.Finish{IR.Log{_, _, _}} IR.Stops{}:
      {==}
    case IR.Finish{IR.Require{IR.Eq{left, right}}} IR.Stops{}:
      require_step(Nat.is_eq(IR.eval(left, env), IR.eval(right, env)), R, k(Unit{}, s), k(Unit{}, s), {==})
    case IR.Finish{IR.Require{IR.Lt{left, right}}} IR.Stops{}:
      require_step(Nat.is_lt(IR.eval(left, env), IR.eval(right, env)), R, k(Unit{}, s), k(Unit{}, s), {==})
    case IR.Finish{IR.SStore{_, _}} IR.Returns{}:
      {==}
    case IR.Finish{IR.Log{_, _, _}} IR.Returns{}:
      {==}
    case IR.Finish{IR.Require{_}} IR.Returns{}:
      {==}
    case IR.Stop{} IR.Stops{}:
      {==}
    case IR.Stop{} IR.Returns{}:
      {==}
