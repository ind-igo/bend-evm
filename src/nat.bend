import Base

# Nat and Bool facts for proofs. In `%e : P`,
# e : {a == b} rewrites b to a, so facts that simplify a term state it on
# the right.

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

def add_zero(+n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n+(+p):
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def sub_zero(+n: Nat) -> {n == Nat.sub(n, 0n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+_:
      {==}

# b >= n, so b - n + n = b.
def sub_add(+b: Nat, +n: Nat, +e: {False{} == Nat.is_lt(b, n) : Bool}) -> {Nat.add(Nat.sub(b, n), n) == b : Nat}:
  match b n:
    case +x 0n:
      %sub_zero(x) : {Nat.add(_, 0n) == x : Nat}
      add_zero(x)
    case 0n 1n+(+m):
      absurd({Nat.add(Nat.sub(0n, 1n+m), 1n+m) == 0n : Nat}, Equal.sym(Bool, False{}, True{}, e))
    case 1n+(+x) 1n+(+m):
      %Equal.sym(Nat, Nat.add(Nat.sub(x, m), 1n+m), 1n+Nat.add(Nat.sub(x, m), m), add_succ(Nat.sub(x, m), m)) :
        {_ == 1n+x : Nat}
      %sub_add(x, m, e) : {1n+Nat.add(Nat.sub(x, m), m) == 1n+_ : Nat}
      {==}

def eq_sound(+x: Nat, +y: Nat, +e: {True{} == Nat.is_eq(x, y) : Bool}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+(+q):
      absurd({0n == 1n+q : Nat}, e)
    case 1n+(+p) 0n:
      absurd({1n+p == 0n : Nat}, e)
    case 1n+(+p) 1n+(+q):
      %eq_sound(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# (p + q) + (r + s) = (p + r) + (q + s).
def swap4(+p: Nat, +q: Nat, +r: Nat, +s: Nat) -> {Nat.add(Nat.add(p, q), Nat.add(r, s)) == Nat.add(Nat.add(p, r), Nat.add(q, s)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(p, q), Nat.add(r, s)), Nat.add(p, Nat.add(q, Nat.add(r, s))), add_assoc(p, q, Nat.add(r, s))) :
    {_ == Nat.add(Nat.add(p, r), Nat.add(q, s)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(p, r), Nat.add(q, s)), Nat.add(p, Nat.add(r, Nat.add(q, s))), add_assoc(p, r, Nat.add(q, s))) :
    {Nat.add(p, Nat.add(q, Nat.add(r, s))) == _ : Nat}
  %add_assoc(q, r, s) : {Nat.add(p, _) == Nat.add(p, Nat.add(r, Nat.add(q, s))) : Nat}
  %add_assoc(r, q, s) : {Nat.add(p, Nat.add(Nat.add(q, r), s)) == Nat.add(p, _) : Nat}
  %add_comm(q, r) : {Nat.add(p, Nat.add(Nat.add(q, r), s)) == Nat.add(p, Nat.add(_, s)) : Nat}
  {==}

# k + x = k + y, so x = y.
def cancel_left(+k: Nat, +x: Nat, +y: Nat, +e: {Nat.add(k, x) == Nat.add(k, y) : Nat}) -> {x == y : Nat}:
  match k:
    case 0n:
      e
    case 1n+(+j):
      cancel_left(j, x, y, Equal.cong(Nat, Nat, pred, 1n+Nat.add(j, x), 1n+Nat.add(j, y), e))

# x + k = y + k, so x = y.
def cancel(+x: Nat, +y: Nat, +k: Nat, +e: {Nat.add(x, k) == Nat.add(y, k) : Nat}) -> {x == y : Nat}:
  cancel_left(k, x, y, Equal.trans(Nat, Nat.add(k, x), Nat.add(x, k), Nat.add(k, y), add_comm(k, x),
    Equal.trans(Nat, Nat.add(x, k), Nat.add(y, k), Nat.add(k, y), e, add_comm(y, k))))

def eq_refl(+x: Nat) -> {True{} == Nat.is_eq(x, x) : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+(+p):
      eq_refl(p)

# (k + x) - k = x.
def sub_add_cancel(+x: Nat, +k: Nat) -> {x == Nat.sub(Nat.add(k, x), k) : Nat}:
  match k:
    case 0n:
      sub_zero(x)
    case 1n+(+j):
      sub_add_cancel(x, j)

# Order facts.

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

# c < 0 never holds.
def no_lt_zero(+c: Nat, +e: {True{} == Nat.is_lt(c, 0n) : Bool}) -> {True{} == False{} : Bool}:
  Equal.trans(Bool, True{}, Nat.is_lt(c, 0n), False{}, e, Equal.sym(Bool, False{}, Nat.is_lt(c, 0n), lt_zero(c)))

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

def and_left(+x: Bool, +y: Bool, +e: {True{} == Bool.and(x, y) : Bool}) -> {True{} == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      e

def and_right(+x: Bool, +y: Bool, +e: {True{} == Bool.and(x, y) : Bool}) -> {True{} == y : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      absurd({True{} == y : Bool}, e)

# Multiplication and division facts.

def mul_zero(+a: Nat) -> {0n == Nat.mul(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      mul_zero(p)

# p + (b + x) = b + (p + x).
def add_swap(+p: Nat, +b: Nat, +x: Nat) -> {Nat.add(p, Nat.add(b, x)) == Nat.add(b, Nat.add(p, x)) : Nat}:
  %add_assoc(p, b, x) : {_ == Nat.add(b, Nat.add(p, x)) : Nat}
  %add_assoc(b, p, x) : {Nat.add(Nat.add(p, b), x) == _ : Nat}
  %add_comm(b, p) : {Nat.add(_, x) == Nat.add(Nat.add(b, p), x) : Nat}
  {==}

def mul_succ(+a: Nat, +b: Nat) -> {Nat.add(a, Nat.mul(a, b)) == Nat.mul(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      %mul_succ(p, b) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+Nat.add(b, _) : Nat}
      %add_swap(p, b, Nat.mul(p, b)) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+_ : Nat}
      {==}

# Nat.div(p, 1 + q) runs Nat.divmod.go(p, q, 0, 0). It takes p one at a
# time: m counts what the current block of 1 + q still needs, r what it
# has, and d the full blocks.

# go takes k at a time into a block that needs k more.
def go_take(+k: Nat, +n: Nat, +m: Nat, +d: Nat, +r: Nat) ->
  {Nat.divmod.go(n, m, d, Nat.add(k, r)) == Nat.divmod.go(Nat.add(k, n), Nat.add(k, m), d, r) : Nat & Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      %add_succ(j, r) : {Nat.divmod.go(n, m, d, _) == Nat.divmod.go(Nat.add(j, n), Nat.add(j, m), d, 1n+r) : Nat & Nat}
      go_take(j, n, m, d, 1n+r)

# One more full block before gives one more in the quotient.
def go_more(n: Nat, +m: Nat, +d: Nat, +r: Nat) ->
  {1n+Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)) == Pair.fst(Nat, Nat, Nat.divmod.go(n, m, 1n+d, r)) : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      go_more(np, r, 1n+d, 0n)
    case 1n+np 1n+mp:
      go_more(np, mp, d, 1n+r)

# p < 1 + q, so q < p is false.
def lt_succ_flip(+p: Nat, +q: Nat, +e: {True{} == Nat.is_lt(p, 1n+q) : Bool}) -> {False{} == Nat.is_lt(q, p) : Bool}:
  %lt_flip(q, p) : {False{} == _ : Bool}
  %e : {False{} == Bool.not(_) : Bool}
  {==}

# p < 1 + q: the quotient is 0 and the remainder p.
def divmod_small(+p: Nat, +q: Nat, +e: {True{} == Nat.is_lt(p, 1n+q) : Bool}) -> {(0n, p) == Nat.divmod(p, 1n+q) : Nat & Nat}:
  +t = Nat.sub(q, p)
  %sub_add(q, p, lt_succ_flip(p, q, e)) : {(0n, p) == Nat.divmod.go(p, _, 0n, 0n) : Nat & Nat}
  %add_comm(p, t) : {(0n, p) == Nat.divmod.go(p, _, 0n, 0n) : Nat & Nat}
  %add_zero(p) : {(0n, _) == Nat.divmod.go(_, Nat.add(p, t), 0n, 0n) : Nat & Nat}
  go_take(p, 0n, t, 0n, 0n)

def div_small(+p: Nat, +q: Nat, +e: {True{} == Nat.is_lt(p, 1n+q) : Bool}) -> {0n == Nat.div(p, 1n+q) : Nat}:
  %divmod_small(p, q, e) : {0n == Pair.fst(Nat, Nat, _) : Nat}
  {==}

def mod_small(+p: Nat, +q: Nat, +e: {True{} == Nat.is_lt(p, 1n+q) : Bool}) -> {p == Nat.mod(p, 1n+q) : Nat}:
  %divmod_small(p, q, e) : {p == Pair.snd(Nat, Nat, _) : Nat}
  {==}

# p >= 1 + q: one block of 1 + q, then the rest.
def div_big(+p: Nat, +q: Nat, +e: {False{} == Nat.is_lt(p, 1n+q) : Bool}) ->
  {1n+Nat.div(Nat.sub(p, 1n+q), 1n+q) == Nat.div(p, 1n+q) : Nat}:
  +t = Nat.sub(p, 1n+q)
  %sub_add(p, 1n+q, e) : {1n+Nat.div(t, 1n+q) == Pair.fst(Nat, Nat, Nat.divmod.go(_, q, 0n, 0n)) : Nat}
  %Equal.sym(Nat, Nat.add(t, 1n+q), 1n+Nat.add(t, q), add_succ(t, q)) :
    {1n+Nat.div(t, 1n+q) == Pair.fst(Nat, Nat, Nat.divmod.go(_, q, 0n, 0n)) : Nat}
  %add_comm(q, t) : {1n+Nat.div(t, 1n+q) == Pair.fst(Nat, Nat, Nat.divmod.go(1n+_, q, 0n, 0n)) : Nat}
  %add_succ(q, t) : {1n+Nat.div(t, 1n+q) == Pair.fst(Nat, Nat, Nat.divmod.go(_, q, 0n, 0n)) : Nat}
  %add_zero(q) : {1n+Nat.div(t, 1n+q) == Pair.fst(Nat, Nat, Nat.divmod.go(Nat.add(q, 1n+t), _, 0n, 0n)) : Nat}
  %go_take(q, 1n+t, 0n, 0n, 0n) : {1n+Nat.div(t, 1n+q) == Pair.fst(Nat, Nat, _) : Nat}
  %Equal.sym(Nat, Nat.add(q, 0n), q, add_zero(q)) :
    {1n+Nat.div(t, 1n+q) == Pair.fst(Nat, Nat, Nat.divmod.go(t, _, 1n, 0n)) : Nat}
  go_more(t, q, 0n, 0n)

# p < a, so a + m > p.
def lt_add_small(+p: Nat, +a: Nat, +m: Nat, +e: {True{} == Nat.is_lt(p, a) : Bool}) ->
  {False{} == Nat.is_lt(Nat.add(a, m), 1n+p) : Bool}:
  match p a:
    case +x 0n:
      absurd({False{} == Nat.is_lt(m, 1n+x) : Bool}, no_lt_zero(x, e))
    case 0n 1n+(+b):
      lt_zero(Nat.add(b, m))
    case 1n+(+c) 1n+(+b):
      lt_add_small(c, b, m, e)

# a <= p, so a + m <= p exactly when m <= p - a.
def lt_add_shift(+p: Nat, +a: Nat, +m: Nat, +e: {False{} == Nat.is_lt(p, a) : Bool}) ->
  {Nat.is_lt(m, 1n+Nat.sub(p, a)) == Nat.is_lt(Nat.add(a, m), 1n+p) : Bool}:
  match p a:
    case +x 0n:
      %sub_zero(x) : {Nat.is_lt(m, 1n+_) == Nat.is_lt(m, 1n+x) : Bool}
      {==}
    case 0n 1n+(+b):
      absurd({Nat.is_lt(m, 1n+Nat.sub(0n, 1n+b)) == Nat.is_lt(Nat.add(1n+b, m), 1n) : Bool}, Equal.sym(Bool, False{}, True{}, e))
    case 1n+(+c) 1n+(+b):
      lt_add_shift(c, b, m, e)

def floor.step(+q: Nat, +c: Nat, +p: Nat, +t: Bool, +et: {t == Nat.is_lt(p, 1n+q) : Bool},
  +ih: {Bool.not(Nat.is_lt(Nat.div(Nat.sub(p, 1n+q), 1n+q), c)) == Nat.is_lt(Nat.mul(1n+q, c), 1n+Nat.sub(p, 1n+q)) : Bool}) ->
  {Bool.not(Nat.is_lt(Nat.div(p, 1n+q), 1n+c)) == Nat.is_lt(Nat.mul(1n+q, 1n+c), 1n+p) : Bool}:
  match t:
    case True{}:
      %div_small(p, q, et) : {Bool.not(Nat.is_lt(_, 1n+c)) == Nat.is_lt(Nat.mul(1n+q, 1n+c), 1n+p) : Bool}
      %mul_succ(1n+q, c) : {False{} == Nat.is_lt(_, 1n+p) : Bool}
      lt_add_small(p, 1n+q, Nat.mul(1n+q, c), et)
    case False{}:
      +d = Nat.div(Nat.sub(p, 1n+q), 1n+q)
      %div_big(p, q, et) : {Bool.not(Nat.is_lt(_, 1n+c)) == Nat.is_lt(Nat.mul(1n+q, 1n+c), 1n+p) : Bool}
      %mul_succ(1n+q, c) : {Bool.not(Nat.is_lt(d, c)) == Nat.is_lt(_, 1n+p) : Bool}
      %lt_add_shift(p, 1n+q, Nat.mul(1n+q, c), et) : {Bool.not(Nat.is_lt(d, c)) == _ : Bool}
      ih

# Floor division: b <= p / a exactly when a * b <= p, for a = 1 + q.
def floor(+q: Nat, b: Nat, +p: Nat) -> {Bool.not(Nat.is_lt(Nat.div(p, 1n+q), b)) == Nat.is_lt(Nat.mul(1n+q, b), 1n+p) : Bool}:
  match b:
    case 0n:
      %mul_zero(q) : {Bool.not(Nat.is_lt(Nat.div(p, 1n+q), 0n)) == Nat.is_lt(_, 1n+p) : Bool}
      %lt_zero(Nat.div(p, 1n+q)) : {Bool.not(_) == Nat.is_lt(0n, 1n+p) : Bool}
      {==}
    case 1n+(+c):
      floor.step(q, c, p, Nat.is_lt(p, 1n+q), {==}, floor(q, c, Nat.sub(p, 1n+q)))

def lt_add_self(+n: Nat, +x: Nat) -> {False{} == Nat.is_lt(Nat.add(n, x), n) : Bool}:
  match n:
    case 0n:
      lt_zero(x)
    case 1n+(+k):
      lt_add_self(k, x)

def not_false(+c: Bool, +e: {Bool.not(c) == False{} : Bool}) -> {True{} == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      absurd({True{} == False{} : Bool}, e)

# p / a <= p.
def div_le(+p: Nat, +q: Nat) -> {True{} == Nat.is_lt(Nat.div(p, 1n+q), 1n+p) : Bool}:
  not_false(Nat.is_lt(Nat.div(p, 1n+q), 1n+p),
    Equal.trans(Bool, Bool.not(Nat.is_lt(Nat.div(p, 1n+q), 1n+p)), Nat.is_lt(Nat.mul(1n+q, 1n+p), 1n+p), False{},
      floor(q, 1n+p, p), Equal.sym(Bool, False{}, Nat.is_lt(Nat.mul(1n+q, 1n+p), 1n+p), lt_add_self(1n+p, Nat.mul(q, 1n+p)))))
