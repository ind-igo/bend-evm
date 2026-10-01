import Base
import ../../src/Evm.bend as Evm
import ../../src/calls.bend as Calls
import ../../src/nat.bend as N
import ../erc20/ERC20.bend as ERC20
import ./Pair.bend as Pair
import ./CERT.bend as Cert
import ./LAWS.bend as Laws

# ---- x·y after a swap ----
#
# The swap reverts or raises at each check, stops at each call, and runs the
# callbacks in the answers. A lemma for each step takes the rest of the run
# as a function, so it holds for any state that the callbacks leave. Checks
# are split by passing their conditions as Bool parameters: matching one
# decides the pick that it controls.

def at(+storage: List<&2, Evm.Slot>, +n: Nat) -> Nat:
  Evm.lookup(storage, Evm.Plain{n})

def ok(-A: Data) -> A -> Evm.State -> Evm.Outcome<A>:
  x => t => Evm.Ok{x, t}

def closed(steps: List<&2, Calls.Step>, o: Evm.Outcome<Unit>) -> Evm.Outcome<Unit>:
  Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, False{}, o)

def opened(steps: List<&2, Calls.Step>, s: Evm.State) -> Evm.Outcome<Unit>:
  Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, True{}, Evm.Ok{Unit{}, s})

# A property of an outcome, which Revert and Raise have.
def keeps(+k: Nat) -> Evm.Outcome<Unit> -> Bool:
  o => Laws.kept(k, o)

def closed_revert(steps: List<&2, Calls.Step>, -p: Evm.Outcome<Unit> -> Bool, +h: {True{} == p(Evm.Revert{}) : Bool}) ->
  {True{} == p(closed(steps, Evm.Revert{})) : Bool}:
  match steps:
    case Nil{}:
      h
    case step <> _:
      match step:
        case Calls.Enter{_, _, _, _}:
          h
        case Calls.Answer{_, _, _}:
          h

def closed_raise(steps: List<&2, Calls.Step>, -e: Evm.Error, -p: Evm.Outcome<Unit> -> Bool, +h: {True{} == p(Evm.Raise{e}) : Bool}) ->
  {True{} == p(closed(steps, Evm.Raise{e})) : Bool}:
  match steps:
    case Nil{}:
      h
    case step <> _:
      match step:
        case Calls.Enter{_, _, _, _}:
          h
        case Calls.Answer{_, _, _}:
          h

def closed_ok(steps: List<&2, Calls.Step>, -t: Evm.State, -p: Evm.Outcome<Unit> -> Bool, +h: {True{} == p(Evm.Ok{Unit{}, t}) : Bool}) ->
  {True{} == p(closed(steps, Evm.Ok{Unit{}, t})) : Bool}:
  match steps:
    case Nil{}:
      h
    case step <> _:
      match step:
        case Calls.Enter{_, _, _, _}:
          h
        case Calls.Answer{_, _, _}:
          h

def pick_keep(+b: Bool, -x: Evm.Outcome<Unit>, -y: Evm.Outcome<Unit>, -p: Evm.Outcome<Unit> -> Bool,
  hx: {True{} == b : Bool} -> {True{} == p(x) : Bool},
  hy: {False{} == b : Bool} -> {True{} == p(y) : Bool}) ->
  {True{} == p(Bool.pick(Evm.Outcome<Unit>, b, x, y)) : Bool}:
  match b:
    case True{}:
      hx({==})
    case False{}:
      hy({==})

def closed_pick(-steps: List<&2, Calls.Step>, +b: Bool, -x: Evm.Outcome<Unit>, -y: Evm.Outcome<Unit>, -p: Evm.Outcome<Unit> -> Bool,
  hx: {True{} == b : Bool} -> {True{} == p(closed(steps, x)) : Bool},
  hy: {False{} == b : Bool} -> {True{} == p(closed(steps, y)) : Bool}) ->
  {True{} == p(closed(steps, Bool.pick(Evm.Outcome<Unit>, b, x, y))) : Bool}:
  match b:
    case True{}:
      hx({==})
    case False{}:
      hy({==})

# A call keeps a property when the rest of the run keeps it from any state:
# the answer's callbacks may leave any state.
def calling(inner: List<&2, Calls.Step>, +c: Evm.Call, +t: Evm.State, -r: Nat -> Evm.State -> Evm.Outcome<Unit>,
  -p: Evm.Outcome<Unit> -> Bool, +h: {True{} == p(Evm.Revert{}) : Bool},
  hr: @x: Nat -> @rest: List<&2, Calls.Step> -> @u: Evm.State -> {True{} == p(closed(rest, r(x, u))) : Bool}) ->
  {True{} == p(closed(inner, Evm.Calling{c, t, r})) : Bool}:
  match inner:
    case Nil{}:
      h
    case step <> +rest:
      match step:
        case Calls.Enter{_, _, _, _}:
          h
        case Calls.Answer{+q, +cbs, +x}:
          pick_keep(Evm.same.call(q, c), closed(rest, r(x, Calls.after(Unit, t, opened(cbs, t)))), Evm.Revert{}, p,
            _ => hr(x, rest, Calls.after(Unit, t, opened(cbs, t))), _ => h)

# (b0 * c) * (b1 * c) = ((b0 * b1) * c) * c.
def square(+b0: Nat, +b1: Nat, +c: Nat) -> {Nat.mul(Nat.mul(b0, c), Nat.mul(b1, c)) == Nat.mul(Nat.mul(Nat.mul(b0, b1), c), c) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(b0, c), Nat.mul(b1, c)), Nat.mul(b0, Nat.mul(c, Nat.mul(b1, c))),
    N.mul_assoc(b0, c, Nat.mul(b1, c))) : {_ == Nat.mul(Nat.mul(Nat.mul(b0, b1), c), c) : Nat}
  %N.mul_assoc(c, b1, c) : {Nat.mul(b0, _) == Nat.mul(Nat.mul(Nat.mul(b0, b1), c), c) : Nat}
  %N.mul_comm(b1, c) : {Nat.mul(b0, Nat.mul(_, c)) == Nat.mul(Nat.mul(Nat.mul(b0, b1), c), c) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(b1, c), c), Nat.mul(b1, Nat.mul(c, c)), N.mul_assoc(b1, c, c)) :
    {Nat.mul(b0, _) == Nat.mul(Nat.mul(Nat.mul(b0, b1), c), c) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(Nat.mul(b0, b1), c), c), Nat.mul(Nat.mul(b0, b1), Nat.mul(c, c)),
    N.mul_assoc(Nat.mul(b0, b1), c, c)) : {Nat.mul(b0, Nat.mul(b1, Nat.mul(c, c))) == _ : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(b0, b1), Nat.mul(c, c)), Nat.mul(b0, Nat.mul(b1, Nat.mul(c, c))),
    N.mul_assoc(b0, b1, Nat.mul(c, c))) : {Nat.mul(b0, Nat.mul(b1, Nat.mul(c, c))) == _ : Nat}
  {==}

def scaled(+b0: Nat, +b1: Nat, +f0: Nat, +f1: Nat, +l: Nat,
  +h: {False{} == Nat.is_lt(Nat.mul(Nat.sub(Nat.mul(b0, 1000n), f0), Nat.sub(Nat.mul(b1, 1000n), f1)), l) : Bool}) ->
  {False{} == Nat.is_lt(Nat.mul(Nat.mul(Nat.mul(b0, b1), 1000n), 1000n), l) : Bool}:
  %square(b0, b1, 1000n) : {False{} == Nat.is_lt(_, l) : Bool}
  N.le_trans(l, Nat.mul(Nat.mul(b0, 1000n), Nat.sub(Nat.mul(b1, 1000n), f1)), Nat.mul(Nat.mul(b0, 1000n), Nat.mul(b1, 1000n)),
    N.le_trans(l, Nat.mul(Nat.sub(Nat.mul(b0, 1000n), f0), Nat.sub(Nat.mul(b1, 1000n), f1)),
      Nat.mul(Nat.mul(b0, 1000n), Nat.sub(Nat.mul(b1, 1000n), f1)), h,
      N.mul_mono_left(Nat.sub(Nat.mul(b0, 1000n), f0), Nat.mul(b0, 1000n), Nat.sub(Nat.mul(b1, 1000n), f1),
        N.sub_le(Nat.mul(b0, 1000n), f0))),
    N.mul_mono_right(Nat.mul(b0, 1000n), Nat.sub(Nat.mul(b1, 1000n), f1), Nat.mul(b1, 1000n), N.sub_le(Nat.mul(b1, 1000n), f1)))

# The check of a swap bounds x·y: if the balances less the fees, scaled by
# 1000, have a product of at least x·y · 1000², the balances' product is at
# least x·y.
def bound(+b0: Nat, +b1: Nat, +f0: Nat, +f1: Nat, +r0: Nat, +r1: Nat,
  +h: {True{} == Bool.not(Nat.is_lt(Nat.mul(Nat.sub(Nat.mul(b0, 1000n), f0), Nat.sub(Nat.mul(b1, 1000n), f1)),
    Nat.mul(Nat.mul(Nat.mul(r0, r1), 1000n), 1000n))) : Bool}) ->
  {True{} == Bool.not(Nat.is_lt(Nat.mul(b0, b1), Nat.mul(r0, r1))) : Bool}:
  %N.cancel_le(Nat.mul(r0, r1), Nat.mul(b0, b1), 999n,
    N.cancel_le(Nat.mul(Nat.mul(r0, r1), 1000n), Nat.mul(Nat.mul(b0, b1), 1000n), 999n,
      scaled(b0, b1, f0, f1, Nat.mul(Nat.mul(Nat.mul(r0, r1), 1000n), 1000n),
        N.not_true(Nat.is_lt(Nat.mul(Nat.sub(Nat.mul(b0, 1000n), f0), Nat.sub(Nat.mul(b1, 1000n), f1)),
          Nat.mul(Nat.mul(Nat.mul(r0, r1), 1000n), 1000n)), h)))) : {True{} == Bool.not(_) : Bool}
  {==}

# The end of a swap, from the state after both calls. Each condition is a
# parameter, in the order of the checks, and eK ties the last one to x·y.
def check.go(rest: List<&2, Calls.Step>, +who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat, +b0: Nat,
  +b1: Nat, +i0: Nat, +i1: Nat, +st: List<&2, Evm.Slot>, +ca: Nat, +li: Nat, +lo: List<&2, Evm.Log>, +w: Evm.World,
  cl0: Bool, cl1: Bool, cin: Bool, cm0: Bool, cf0: Bool, ca0: Bool, cm1: Bool, cf1: Bool, ca1: Bool, cA: Bool, cB: Bool,
  cS: Bool, cL: Bool, cK: Bool,
  +eK: {cK == Bool.not(Nat.is_lt(Nat.mul(Nat.sub(Nat.mul(b0, 1000n), Nat.mul(i0, 3n)), Nat.sub(Nat.mul(b1, 1000n), Nat.mul(i1, 3n))),
    Nat.mul(Nat.mul(Nat.mul(r0, r1), 1000n), 1000n))) : Bool}) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest,
    Bool.pick(Evm.Outcome<Unit>, cl0, Evm.Revert{},
    Bool.pick(Evm.Outcome<Unit>, cl1, Evm.Revert{},
    Bool.pick(Evm.Outcome<Unit>, cin,
    Bool.pick(Evm.Outcome<Unit>, cm0,
    Bool.pick(Evm.Outcome<Unit>, cf0,
    Bool.pick(Evm.Outcome<Unit>, ca0, Evm.Revert{},
    Bool.pick(Evm.Outcome<Unit>, cm1,
    Bool.pick(Evm.Outcome<Unit>, cf1,
    Bool.pick(Evm.Outcome<Unit>, ca1, Evm.Revert{},
    Bool.pick(Evm.Outcome<Unit>, cA,
    Bool.pick(Evm.Outcome<Unit>, cB,
    Bool.pick(Evm.Outcome<Unit>, cS,
    Bool.pick(Evm.Outcome<Unit>, cL,
    Bool.pick(Evm.Outcome<Unit>, cK,
      Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{6n}, b1} <> Evm.Slot{Evm.Plain{5n}, b0} <> st, ca, li,
        Evm.Log{"Swap", [who, to], [i0, i1, out0, out1]} <> Evm.Log{"Sync", [], [b0, b1]} <> lo, w}},
      Evm.Raise{Pair.K()}),
    Evm.Revert{}), Evm.Revert{}), Evm.Revert{}), Evm.Revert{})),
    Evm.Revert{}), Evm.Revert{})),
    Evm.Revert{}), Evm.Revert{}),
    Evm.Raise{Pair.InsufficientInputAmount()}))))) : Bool}:
  match cl0:
    case True{}:
      closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
    case False{}:
      match cl1:
        case True{}:
          closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
        case False{}:
          match cin:
            case False{}:
              closed_raise(rest, Pair.InsufficientInputAmount(), keeps(Nat.mul(r0, r1)), {==})
            case True{}:
              match cm0:
                case False{}:
                  closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
                case True{}:
                  match cf0:
                    case False{}:
                      closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
                    case True{}:
                      match ca0:
                        case True{}:
                          closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
                        case False{}:
                          match cm1:
                            case False{}:
                              closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
                            case True{}:
                              match cf1:
                                case False{}:
                                  closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
                                case True{}:
                                  match ca1:
                                    case True{}:
                                      closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
                                    case False{}:
                                      match cA:
                                        case False{}:
                                          closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
                                        case True{}:
                                          match cB:
                                            case False{}:
                                              closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
                                            case True{}:
                                              match cS:
                                                case False{}:
                                                  closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
                                                case True{}:
                                                  match cL:
                                                    case False{}:
                                                      closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
                                                    case True{}:
                                                      match cK:
                                                        case False{}:
                                                          closed_raise(rest, Pair.K(), keeps(Nat.mul(r0, r1)), {==})
                                                        case True{}:
                                                          closed_ok(rest, Evm.State{Evm.Slot{Evm.Plain{6n}, b1} <> Evm.Slot{Evm.Plain{5n}, b0} <> st,
                                                            ca, li, Evm.Log{"Swap", [who, to], [i0, i1, out0, out1]} <> Evm.Log{"Sync", [], [b0, b1]} <> lo, w},
                                                            keeps(Nat.mul(r0, r1)), bound(b0, b1, Nat.mul(i0, 3n), Nat.mul(i1, 3n), r0, r1, eK))

# The amount in of one token: its balance above the reserve left after
# the amount out.
def into(+r: Nat, +out: Nat, +b: Nat, +li: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(Nat.sub(r, out), b), Evm.op(Evm.Sub{}, [b, Nat.sub(r, out)], li), 0n)

def check.at(rest: List<&2, Calls.Step>, +who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat, +b0: Nat,
  +b1: Nat, +st: List<&2, Evm.Slot>, +ca: Nat, +li: Nat, +lo: List<&2, Evm.Log>, +w: Evm.World) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest,
    Pair.check(who, to, out0, out1, r0, r1, b0, b1)(Unit, ok(Unit), Evm.State{st, ca, li, lo, w}))) : Bool}:
  +i0 = into(r0, out0, b0, li)
  +i1 = into(r1, out1, b1, li)
  +a0 = Nat.sub(Nat.mul(b0, 1000n), Nat.mul(i0, 3n))
  +a1 = Nat.sub(Nat.mul(b1, 1000n), Nat.mul(i1, 3n))
  check.go(rest, who, to, out0, out1, r0, r1, b0, b1, i0, i1, st, ca, li, lo, w,
    Nat.is_lt(r0, out0), Nat.is_lt(r1, out1), Nat.is_lt(0n, Evm.op(Evm.Or{}, [i0, i1], li)),
    Nat.is_lt(Nat.mul(b0, 1000n), li), Nat.is_lt(Nat.mul(i0, 3n), li), Nat.is_lt(Nat.mul(b0, 1000n), Nat.mul(i0, 3n)),
    Nat.is_lt(Nat.mul(b1, 1000n), li), Nat.is_lt(Nat.mul(i1, 3n), li), Nat.is_lt(Nat.mul(b1, 1000n), Nat.mul(i1, 3n)),
    Nat.is_lt(Nat.mul(a0, a1), li), Nat.is_lt(Nat.mul(r0, r1), li), Nat.is_lt(Nat.mul(Nat.mul(r0, r1), 1000n), li),
    Nat.is_lt(Nat.mul(Nat.mul(Nat.mul(r0, r1), 1000n), 1000n), li),
    Bool.not(Nat.is_lt(Nat.mul(a0, a1), Nat.mul(Nat.mul(Nat.mul(r0, r1), 1000n), 1000n))), {==})

def balance.of(+st: List<&2, Evm.Slot>, +n: Nat, +self: Nat) -> Evm.Call:
  Evm.Call{at(st, n), "balanceOf", [self]}

# The second balance, from the answers left after the first.
def viewed(+rest: List<&2, Calls.Step>, +who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat, +b0: Nat,
  +st: List<&2, Evm.Slot>, +ca: Nat, +li: Nat, +lo: List<&2, Evm.Log>, +facts: List<&2, Evm.Fact>, +readings: List<&2, Nat>, +self: Nat,
  +hashes: List<&2, Evm.Hashed>, +signers: List<&2, Evm.Signed>, answers: List<&2, Evm.Answer>) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest, Evm.answer(Unit, balance.of(st, 4n, self),
    b1 => v => Pair.check(who, to, out0, out1, r0, r1, b0, b1)(Unit, ok(Unit), v),
    Evm.State{st, ca, li, lo, Evm.World{facts, readings, self, hashes, signers, answers}}))) : Bool}:
  match answers:
    case Nil{}:
      closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
    case Evm.Answer{+q, +b1} <> +more:
      closed_pick(rest, Evm.same.call(q, balance.of(st, 4n, self)),
        Pair.check(who, to, out0, out1, r0, r1, b0, b1)(Unit, ok(Unit),
          Evm.State{st, ca, li, lo, Evm.World{facts, readings, self, hashes, signers, more}}),
        Evm.Revert{}, keeps(Nat.mul(r0, r1)),
        _ => check.at(rest, who, to, out0, out1, r0, r1, b0, b1, st, ca, li, lo, Evm.World{facts, readings, self, hashes, signers, more}),
        _ => closed_revert(rest, keeps(Nat.mul(r0, r1)), {==}))

# settle from any state: the callbacks may leave any storage and answers.
def settled(+rest: List<&2, Calls.Step>, +who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat, u: Evm.State) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest, Pair.settle(who, to, out0, out1, r0, r1)(Unit, ok(Unit), u))) : Bool}:
  match u:
    case Evm.State{+st, +ca, +li, +lo, Evm.World{+facts, +readings, +self, +hashes, +signers, answers}}:
      match answers:
        case Nil{}:
          closed_revert(rest, keeps(Nat.mul(r0, r1)), {==})
        case Evm.Answer{+q, +b0} <> +more:
          closed_pick(rest, Evm.same.call(q, balance.of(st, 3n, self)),
            Evm.answer(Unit, balance.of(st, 4n, self), b1 => v => Pair.check(who, to, out0, out1, r0, r1, b0, b1)(Unit, ok(Unit), v),
              Evm.State{st, ca, li, lo, Evm.World{facts, readings, self, hashes, signers, more}}),
            Evm.Revert{}, keeps(Nat.mul(r0, r1)),
            _ => viewed(rest, who, to, out0, out1, r0, r1, b0, st, ca, li, lo, facts, readings, self, hashes, signers, more),
            _ => closed_revert(rest, keeps(Nat.mul(r0, r1)), {==}))

# The end of a swap after both payments: settle, or with data a flash
# swap's call first, which may leave any state.
def ending(+who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat, +data: Evm.Bytes) -> Evm.Contract(Unit):
  Evm.branch(Unit, Nat.is_eq(Evm.length(data), 0n), Pair.settle(who, to, out0, out1, r0, r1),
    Pair.flash(who, to, out0, out1, r0, r1, data))

def ended(c: Bool, +rest: List<&2, Calls.Step>, +u: Evm.State, +who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat,
  +data: Evm.Bytes) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest, Evm.branch(Unit, c, Pair.settle(who, to, out0, out1, r0, r1),
    Pair.flash(who, to, out0, out1, r0, r1, data))(Unit, ok(Unit), u))) : Bool}:
  match c:
    case True{}:
      settled(rest, who, to, out0, out1, r0, r1, u)
    case False{}:
      calling(rest, Evm.Call{to, "uniswapV2Call", Evm.abi([Evm.Word{who}, Evm.Word{out0}, Evm.Word{out1}, Evm.Dynamic{data}])}, u,
        _ => t => Pair.settle(who, to, out0, out1, r0, r1)(Unit, ok(Unit), t), keeps(Nat.mul(r0, r1)), {==},
        _ => more => v => settled(more, who, to, out0, out1, r0, r1, v))

# After the second call: the token must return 1.
def paid1(+x: Nat, +rest: List<&2, Calls.Step>, +u: Evm.State, +who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat,
  +data: Evm.Bytes) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest, Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n),
    ending(who, to, out0, out1, r0, r1, data)(Unit, ok(Unit), u), Evm.Raise{Pair.TransferFailed()}))) : Bool}:
  closed_pick(rest, Nat.is_eq(x, 1n), ending(who, to, out0, out1, r0, r1, data)(Unit, ok(Unit), u), Evm.Raise{Pair.TransferFailed()},
    keeps(Nat.mul(r0, r1)),
    _ => ended(Nat.is_eq(Evm.length(data), 0n), rest, u, who, to, out0, out1, r0, r1, data),
    _ => closed_raise(rest, Pair.TransferFailed(), keeps(Nat.mul(r0, r1)), {==}))

def after1(+who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat, +data: Evm.Bytes) -> Nat -> Evm.State -> Evm.Outcome<Unit>:
  x => u => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n), ending(who, to, out0, out1, r0, r1, data)(Unit, ok(Unit), u),
    Evm.Raise{Pair.TransferFailed()})

# After the first call: the token must return 1, then the second call.
def paid0(+x: Nat, +rest: List<&2, Calls.Step>, +u: Evm.State, +who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat,
  +t1: Nat, +data: Evm.Bytes) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest, Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n),
    Pair.pay(t1, to, out1)(Unit, v => w => ending(who, to, out0, out1, r0, r1, data)(Unit, ok(Unit), w), u),
    Evm.Raise{Pair.TransferFailed()}))) : Bool}:
  closed_pick(rest, Nat.is_eq(x, 1n), Pair.pay(t1, to, out1)(Unit, v => w => ending(who, to, out0, out1, r0, r1, data)(Unit, ok(Unit), w), u),
    Evm.Raise{Pair.TransferFailed()}, keeps(Nat.mul(r0, r1)),
    _ => calling(rest, Evm.Call{t1, "transfer", [to, out1]}, u, after1(who, to, out0, out1, r0, r1, data), keeps(Nat.mul(r0, r1)), {==},
      y => more => v => paid1(y, more, v, who, to, out0, out1, r0, r1, data)),
    _ => closed_raise(rest, Pair.TransferFailed(), keeps(Nat.mul(r0, r1)), {==}))

def after0(+who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat, +t1: Nat, +data: Evm.Bytes) -> Nat -> Evm.State -> Evm.Outcome<Unit>:
  x => u => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n),
    Pair.pay(t1, to, out1)(Unit, v => w => ending(who, to, out0, out1, r0, r1, data)(Unit, ok(Unit), w), u),
    Evm.Raise{Pair.TransferFailed()})

# The checks before the first call, then the call.
def top(steps: List<&2, Calls.Step>, +st: List<&2, Evm.Slot>, +ca: Nat, +li: Nat, +lo: List<&2, Evm.Log>, +w: Evm.World,
  +out0: Nat, +out1: Nat, +to: Nat, +data: Evm.Bytes, c1: Bool, c2: Bool, c3: Bool, c4: Bool, c5: Bool) ->
  {True{} == Laws.kept(Nat.mul(at(st, 5n), at(st, 6n)), closed(steps,
    Bool.pick(Evm.Outcome<Unit>, c1,
    Bool.pick(Evm.Outcome<Unit>, c2,
    Bool.pick(Evm.Outcome<Unit>, c3,
    Bool.pick(Evm.Outcome<Unit>, c4,
    Bool.pick(Evm.Outcome<Unit>, c5,
      Evm.Calling{Evm.Call{at(st, 3n), "transfer", [to, out0]}, Evm.State{st, ca, li, lo, w},
        after0(ca, to, out0, out1, at(st, 5n), at(st, 6n), at(st, 4n), data)},
      Evm.Raise{Pair.InvalidTo()}), Evm.Raise{Pair.InvalidTo()}),
      Evm.Raise{Pair.InsufficientLiquidity()}), Evm.Raise{Pair.InsufficientLiquidity()}),
      Evm.Raise{Pair.InsufficientOutputAmount()}))) : Bool}:
  match c1:
    case False{}:
      closed_raise(steps, Pair.InsufficientOutputAmount(), keeps(Nat.mul(at(st, 5n), at(st, 6n))), {==})
    case True{}:
      match c2:
        case False{}:
          closed_raise(steps, Pair.InsufficientLiquidity(), keeps(Nat.mul(at(st, 5n), at(st, 6n))), {==})
        case True{}:
          match c3:
            case False{}:
              closed_raise(steps, Pair.InsufficientLiquidity(), keeps(Nat.mul(at(st, 5n), at(st, 6n))), {==})
            case True{}:
              match c4:
                case False{}:
                  closed_raise(steps, Pair.InvalidTo(), keeps(Nat.mul(at(st, 5n), at(st, 6n))), {==})
                case True{}:
                  match c5:
                    case False{}:
                      closed_raise(steps, Pair.InvalidTo(), keeps(Nat.mul(at(st, 5n), at(st, 6n))), {==})
                    case True{}:
                      calling(steps, Evm.Call{at(st, 3n), "transfer", [to, out0]}, Evm.State{st, ca, li, lo, w},
                        after0(ca, to, out0, out1, at(st, 5n), at(st, 6n), at(st, 4n), data), keeps(Nat.mul(at(st, 5n), at(st, 6n))), {==},
                        x => rest => u => paid0(x, rest, u, ca, to, out0, out1, at(st, 5n), at(st, 6n), at(st, 4n), data))

def Laws.swap(steps, s, amount0Out, amount1Out, to, data):
  match s:
    case Evm.State{+st, +ca, +li, +lo, +w}:
      top(steps, st, ca, li, lo, w, amount0Out, amount1Out, to, data,
        Nat.is_lt(0n, Evm.op(Evm.Or{}, [amount0Out, amount1Out], li)), Nat.is_lt(amount0Out, at(st, 5n)),
        Nat.is_lt(amount1Out, at(st, 6n)), Bool.not(Nat.is_eq(to, at(st, 3n))), Bool.not(Nat.is_eq(to, at(st, 4n))))

def Laws.sync(storage, caller, limit, logs, facts, readings, self, hashes, signers, q0, b0, q1, b1, more):
  {==}

# ---- A mint does not dilute ----

def lt_asym(+x: Nat, +y: Nat, +e: {True{} == Nat.is_lt(x, y) : Bool}) -> {False{} == Nat.is_lt(y, x) : Bool}:
  match x y:
    case 0n 0n:
      N.absurd({False{} == Nat.is_lt(0n, 0n) : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      N.absurd({False{} == Nat.is_lt(0n, 1n+p) : Bool}, e)
    case 1n+p 1n+q:
      lt_asym(p, q, e)

# The smaller of s0 and s1 is at most each.
def min_left(c: Bool, +s0: Nat, +s1: Nat, +ec: {c == Nat.is_lt(s0, s1) : Bool}) ->
  {False{} == Nat.is_lt(s0, Bool.pick(Nat, c, s0, s1)) : Bool}:
  match c:
    case True{}:
      N.lt_irrefl(s0)
    case False{}:
      ec

def min_right(c: Bool, +s0: Nat, +s1: Nat, +ec: {c == Nat.is_lt(s0, s1) : Bool}) ->
  {False{} == Nat.is_lt(s1, Bool.pick(Nat, c, s0, s1)) : Bool}:
  match c:
    case True{}:
      lt_asym(s0, s1, ec)
    case False{}:
      N.lt_irrefl(s1)

def not_irrefl(+d: Nat) -> {True{} == Bool.not(Nat.is_lt(d, d)) : Bool}:
  %N.lt_irrefl(d) : {True{} == Bool.not(_) : Bool}
  {==}

# (p / r) * r <= p, as r * (p / r) <= p.
def floored(+q: Nat, +p: Nat) -> {False{} == Nat.is_lt(p, Nat.mul(Nat.div(p, 1n+q), 1n+q)) : Bool}:
  %N.mul_comm(1n+q, Nat.div(p, 1n+q)) : {False{} == Nat.is_lt(p, _) : Bool}
  N.lt_succ_flip(Nat.mul(1n+q, Nat.div(p, 1n+q)), p,
    Equal.trans(Bool, True{}, Bool.not(Nat.is_lt(Nat.div(p, 1n+q), Nat.div(p, 1n+q))), Nat.is_lt(Nat.mul(1n+q, Nat.div(p, 1n+q)), 1n+p),
      not_irrefl(Nat.div(p, 1n+q)), N.floor(q, Nat.div(p, 1n+q), p)))

def share.go(+s: Nat, +l: Nat, +b: Nat, +q: Nat,
  +hl: {False{} == Nat.is_lt(Nat.div(Nat.mul(Nat.sub(b, 1n+q), s), 1n+q), l) : Bool},
  +hr: {False{} == Nat.is_lt(b, 1n+q) : Bool}) ->
  {False{} == Nat.is_lt(Nat.mul(s, b), Nat.mul(Nat.add(s, l), 1n+q)) : Bool}:
  %N.sub_add(b, 1n+q, hr) : {False{} == Nat.is_lt(Nat.mul(s, _), Nat.mul(Nat.add(s, l), 1n+q)) : Bool}
  %N.mul_comm(Nat.add(Nat.sub(b, 1n+q), 1n+q), s) : {False{} == Nat.is_lt(_, Nat.mul(Nat.add(s, l), 1n+q)) : Bool}
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.sub(b, 1n+q), 1n+q), s), Nat.add(Nat.mul(Nat.sub(b, 1n+q), s), Nat.mul(1n+q, s)),
    N.mul_add(Nat.sub(b, 1n+q), 1n+q, s)) : {False{} == Nat.is_lt(_, Nat.mul(Nat.add(s, l), 1n+q)) : Bool}
  %N.mul_comm(s, 1n+q) : {False{} == Nat.is_lt(Nat.add(Nat.mul(Nat.sub(b, 1n+q), s), _), Nat.mul(Nat.add(s, l), 1n+q)) : Bool}
  %N.add_comm(Nat.mul(s, 1n+q), Nat.mul(Nat.sub(b, 1n+q), s)) : {False{} == Nat.is_lt(_, Nat.mul(Nat.add(s, l), 1n+q)) : Bool}
  %Equal.sym(Nat, Nat.mul(Nat.add(s, l), 1n+q), Nat.add(Nat.mul(s, 1n+q), Nat.mul(l, 1n+q)), N.mul_add(s, l, 1n+q)) :
    {False{} == Nat.is_lt(Nat.add(Nat.mul(s, 1n+q), Nat.mul(Nat.sub(b, 1n+q), s)), _) : Bool}
  N.add_mono_left(Nat.mul(s, 1n+q), Nat.mul(l, 1n+q), Nat.mul(Nat.sub(b, 1n+q), s),
    N.le_trans(Nat.mul(l, 1n+q), Nat.mul(Nat.div(Nat.mul(Nat.sub(b, 1n+q), s), 1n+q), 1n+q), Nat.mul(Nat.sub(b, 1n+q), s),
      N.mul_mono_left(l, Nat.div(Nat.mul(Nat.sub(b, 1n+q), s), 1n+q), 1n+q, hl),
      floored(q, Nat.mul(Nat.sub(b, 1n+q), s))))

# A minter who gets l <= (b - r) * s / r liquidity tokens, for supply s and
# reserve r of a token whose balance is b, leaves s * b >= (s + l) * r.
def share(+s: Nat, +l: Nat, +b: Nat, r: Nat,
  +hl: {False{} == Nat.is_lt(Nat.div(Nat.mul(Nat.sub(b, r), s), r), l) : Bool},
  +hr: {False{} == Nat.is_lt(b, r) : Bool}, +hz: {False{} == Nat.is_eq(r, 0n) : Bool}) ->
  {False{} == Nat.is_lt(Nat.mul(s, b), Nat.mul(Nat.add(s, l), r)) : Bool}:
  match r:
    case 0n:
      N.absurd({False{} == Nat.is_lt(Nat.mul(s, b), Nat.mul(Nat.add(s, l), 0n)) : Bool}, Equal.sym(Bool, False{}, True{}, hz))
    case 1n+q:
      share.go(s, l, b, q, hl, hr)

def both(+x: Bool, +y: Bool, +hx: {False{} == x : Bool}, +hy: {False{} == y : Bool}) ->
  {True{} == Bool.and(Bool.not(x), Bool.not(y)) : Bool}:
  %hx : {True{} == Bool.and(Bool.not(_), Bool.not(y)) : Bool}
  %hy : {True{} == Bool.and(Bool.not(False{}), Bool.not(_)) : Bool}
  {==}

def fair_pick(+b: Bool, -x: Evm.Outcome<Nat>, -y: Evm.Outcome<Nat>, -st: List<&2, Evm.Slot>,
  hx: {True{} == b : Bool} -> {True{} == Laws.fair(st, x) : Bool},
  hy: {False{} == b : Bool} -> {True{} == Laws.fair(st, y) : Bool}) ->
  {True{} == Laws.fair(st, Bool.pick(Evm.Outcome<Nat>, b, x, y)) : Bool}:
  match b:
    case True{}:
      hx({==})
    case False{}:
      hy({==})

# The first mint has no bound.
def fair_first(+st: List<&2, Evm.Slot>, o: Evm.Outcome<Nat>, +ez: {True{} == Nat.is_eq(Laws.supply(st), 0n) : Bool}) ->
  {True{} == Laws.fair(st, o) : Bool}:
  match o:
    case Evm.Ok{_, t}:
      match t:
        case Evm.State{+storage, _, _, _, _}:
          %ez : {True{} == Bool.or(_, Laws.gained(st, storage)) : Bool}
          {==}
    case Evm.Revert{}:
      {==}
    case Evm.Raise{_}:
      {==}
    case Evm.Calling{_, _, _}:
      {==}

# The part of the supply s that the balance b above the reserve r buys.
def part(+b: Nat, +r: Nat, +s: Nat) -> Nat:
  Nat.div(Nat.mul(Nat.sub(b, r), s), r)

# The liquidity of a later mint.
def minimum(+b0: Nat, +b1: Nat, +st: List<&2, Evm.Slot>) -> Nat:
  Bool.pick(Nat, Nat.is_lt(part(b0, at(st, 5n), at(st, 0n)), part(b1, at(st, 6n), at(st, 0n))),
    part(b0, at(st, 5n), at(st, 0n)), part(b1, at(st, 6n), at(st, 0n)))

# A later mint, with its checks as parameters.
def more.go(+to: Nat, +b0: Nat, +b1: Nat, +st: List<&2, Evm.Slot>, +ca: Nat, +li: Nat, +lo: List<&2, Evm.Log>, +w: Evm.World,
  +ez: {False{} == Nat.is_eq(at(st, 0n), 0n) : Bool}, +hr0: {False{} == Nat.is_lt(b0, at(st, 5n)) : Bool},
  +hr1: {False{} == Nat.is_lt(b1, at(st, 6n)) : Bool},
  cx: Bool, cd0: Bool, +ed0: {cd0 == Nat.is_eq(at(st, 5n), 0n) : Bool}, cy: Bool, cd1: Bool,
  +ed1: {cd1 == Nat.is_eq(at(st, 6n), 0n) : Bool}, cl: Bool, cadd: Bool, cbal: Bool) ->
  {True{} == Laws.fair(st,
    Bool.pick(Evm.Outcome<Nat>, cx,
    Bool.pick(Evm.Outcome<Nat>, cd0, Evm.Revert{},
    Bool.pick(Evm.Outcome<Nat>, cy,
    Bool.pick(Evm.Outcome<Nat>, cd1, Evm.Revert{},
    Bool.pick(Evm.Outcome<Nat>, cl,
    Bool.pick(Evm.Outcome<Nat>, cadd,
    Bool.pick(Evm.Outcome<Nat>, cbal,
      Evm.Ok{minimum(b0, b1, st), Evm.State{Evm.Slot{Evm.Plain{6n}, b1} <> Evm.Slot{Evm.Plain{5n}, b0}
        <> Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(Evm.lookup(st, Evm.Mapped{Evm.Plain{1n}, to}), minimum(b0, b1, st))}
        <> Evm.Slot{Evm.Plain{0n}, Nat.add(at(st, 0n), minimum(b0, b1, st))} <> st, ca, li,
        Pair.Mint(ca, Nat.sub(b0, at(st, 5n)), Nat.sub(b1, at(st, 6n))) <> Pair.Sync(b0, b1)
        <> Evm.Log{"Transfer", [0n, to], [minimum(b0, b1, st)]} <> lo, w}},
      Evm.Revert{}),
      Evm.Revert{}),
      Evm.Raise{Pair.InsufficientLiquidityMinted()})),
      Evm.Revert{})),
      Evm.Revert{})) : Bool}:
  match cx:
    case False{}:
      {==}
    case True{}:
      match cd0:
        case True{}:
          {==}
        case False{}:
          match cy:
            case False{}:
              {==}
            case True{}:
              match cd1:
                case True{}:
                  {==}
                case False{}:
                  match cl:
                    case False{}:
                      {==}
                    case True{}:
                      match cadd:
                        case False{}:
                          {==}
                        case True{}:
                          match cbal:
                            case False{}:
                              {==}
                            case True{}:
                              %ez : {True{} == Bool.or(_, Laws.gained(st, Evm.Slot{Evm.Plain{6n}, b1} <> Evm.Slot{Evm.Plain{5n}, b0}
                                <> Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(Evm.lookup(st, Evm.Mapped{Evm.Plain{1n}, to}), minimum(b0, b1, st))}
                                <> Evm.Slot{Evm.Plain{0n}, Nat.add(at(st, 0n), minimum(b0, b1, st))} <> st)) : Bool}
                              both(Nat.is_lt(Nat.mul(at(st, 0n), b0), Nat.mul(Nat.add(at(st, 0n), minimum(b0, b1, st)), at(st, 5n))),
                                Nat.is_lt(Nat.mul(at(st, 0n), b1), Nat.mul(Nat.add(at(st, 0n), minimum(b0, b1, st)), at(st, 6n))),
                                share(at(st, 0n), minimum(b0, b1, st), b0, at(st, 5n),
                                  min_left(Nat.is_lt(part(b0, at(st, 5n), at(st, 0n)), part(b1, at(st, 6n), at(st, 0n))),
                                    part(b0, at(st, 5n), at(st, 0n)), part(b1, at(st, 6n), at(st, 0n)), {==}), hr0, ed0),
                                share(at(st, 0n), minimum(b0, b1, st), b1, at(st, 6n),
                                  min_right(Nat.is_lt(part(b0, at(st, 5n), at(st, 0n)), part(b1, at(st, 6n), at(st, 0n))),
                                    part(b0, at(st, 5n), at(st, 0n)), part(b1, at(st, 6n), at(st, 0n)), {==}), hr1, ed1))

# What mint does after it reads the balances.
def mint.rest(+to: Nat, +b0: Nat, +b1: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +r0 : Nat <- Evm.sload(Pair.RESERVE0())
    +r1 : Nat <- Evm.sload(Pair.RESERVE1())
    +amount0 : Nat <- Evm.sub(b0, r0)
    +amount1 : Nat <- Evm.sub(b1, r1)
    +supply : Nat <- Evm.sload(ERC20.SUPPLY())
    Evm.branch(Nat, Nat.is_eq(supply, 0n), Pair.first(to, b0, b1, amount0, amount1),
      Pair.more(to, b0, b1, amount0, amount1, r0, r1, supply))

def mint.go(+to: Nat, +b0: Nat, +b1: Nat, +st: List<&2, Evm.Slot>, +ca: Nat, +li: Nat, +lo: List<&2, Evm.Log>, +w: Evm.World,
  ca0: Bool, +e0: {ca0 == Nat.is_lt(b0, at(st, 5n)) : Bool}, ca1: Bool, +e1: {ca1 == Nat.is_lt(b1, at(st, 6n)) : Bool},
  cz: Bool, +ez: {cz == Nat.is_eq(at(st, 0n), 0n) : Bool}) ->
  {True{} == Laws.fair(st,
    Bool.pick(Evm.Outcome<Nat>, ca0, Evm.Revert{},
    Bool.pick(Evm.Outcome<Nat>, ca1, Evm.Revert{},
      Bool.pick(Evm.Contract(Nat), cz, Pair.first(to, b0, b1, Nat.sub(b0, at(st, 5n)), Nat.sub(b1, at(st, 6n))),
        Pair.more(to, b0, b1, Nat.sub(b0, at(st, 5n)), Nat.sub(b1, at(st, 6n)), at(st, 5n), at(st, 6n), at(st, 0n)))(Nat,
        ok(Nat), Evm.State{st, ca, li, lo, w})))) : Bool}:
  match ca0:
    case True{}:
      {==}
    case False{}:
      match ca1:
        case True{}:
          {==}
        case False{}:
          match cz:
            case True{}:
              fair_first(st, Pair.first(to, b0, b1, Nat.sub(b0, at(st, 5n)), Nat.sub(b1, at(st, 6n)))(Nat, ok(Nat), Evm.State{st, ca, li, lo, w}), ez)
            case False{}:
              more.go(to, b0, b1, st, ca, li, lo, w, ez, e0, e1,
                Nat.is_lt(Nat.mul(Nat.sub(b0, at(st, 5n)), at(st, 0n)), li), Nat.is_eq(at(st, 5n), 0n), {==},
                Nat.is_lt(Nat.mul(Nat.sub(b1, at(st, 6n)), at(st, 0n)), li), Nat.is_eq(at(st, 6n), 0n), {==},
                Nat.is_lt(0n, minimum(b0, b1, st)), Nat.is_lt(Nat.add(at(st, 0n), minimum(b0, b1, st)), li),
                Nat.is_lt(Nat.add(Evm.lookup(st, Evm.Mapped{Evm.Plain{1n}, to}), minimum(b0, b1, st)), li))

def mint.second(+to: Nat, +b0: Nat, +st: List<&2, Evm.Slot>, +ca: Nat, +li: Nat, +lo: List<&2, Evm.Log>, +facts: List<&2, Evm.Fact>,
  +readings: List<&2, Nat>, +self: Nat, +hashes: List<&2, Evm.Hashed>, +signers: List<&2, Evm.Signed>, answers: List<&2, Evm.Answer>) ->
  {True{} == Laws.fair(st, Evm.answer(Nat, balance.of(st, 4n, self), b1 => v => mint.rest(to, b0, b1)(Nat, ok(Nat), v),
    Evm.State{st, ca, li, lo, Evm.World{facts, readings, self, hashes, signers, answers}})) : Bool}:
  match answers:
    case Nil{}:
      {==}
    case Evm.Answer{+q, +b1} <> +more:
      fair_pick(Evm.same.call(q, balance.of(st, 4n, self)),
        mint.rest(to, b0, b1)(Nat, ok(Nat), Evm.State{st, ca, li, lo, Evm.World{facts, readings, self, hashes, signers, more}}),
        Evm.Revert{}, st,
        _ => mint.go(to, b0, b1, st, ca, li, lo, Evm.World{facts, readings, self, hashes, signers, more},
          Nat.is_lt(b0, at(st, 5n)), {==}, Nat.is_lt(b1, at(st, 6n)), {==}, Nat.is_eq(at(st, 0n), 0n), {==}),
        _ => {==})

def Laws.mint(storage, caller, limit, logs, world, to):
  match world:
    case Evm.World{+facts, +readings, +self, +hashes, +signers, answers}:
      match answers:
        case Nil{}:
          {==}
        case Evm.Answer{+q, +b0} <> +more:
          fair_pick(Evm.same.call(q, balance.of(storage, 3n, self)),
            Evm.answer(Nat, balance.of(storage, 4n, self), b1 => v => mint.rest(to, b0, b1)(Nat, ok(Nat), v),
              Evm.State{storage, caller, limit, logs, Evm.World{facts, readings, self, hashes, signers, more}}),
            Evm.Revert{}, storage,
            _ => mint.second(to, b0, storage, caller, limit, logs, facts, readings, self, hashes, signers, more),
            _ => {==})

# ---- A burn pays no more than the share ----

def pays(+l: Nat, +s: Nat, +b0: Nat, +b1: Nat) -> Evm.Outcome<Unit> -> Bool:
  o => Laws.paid(l, s, b0, b1, o)

# (p / s) * s <= p.
def part_le(+p: Nat, s: Nat, +ez: {False{} == Nat.is_eq(s, 0n) : Bool}) -> {False{} == Nat.is_lt(p, Nat.mul(Nat.div(p, s), s)) : Bool}:
  match s:
    case 0n:
      N.absurd({False{} == Nat.is_lt(p, Nat.mul(Nat.div(p, 0n), 0n)) : Bool}, Equal.sym(Bool, False{}, True{}, ez))
    case 1n+q:
      floored(q, p)

# The end of a burn: update and log Burn.
def burn.fin(+who: Nat, +to: Nat, +a0: Nat, +a1: Nat, +c0: Nat, +c1: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    Pair.update(c0, c1)
    Evm.emit(Pair.Burn(who, to, a0, a1))

# What burn does after both calls: sync, then log Burn.
def burn.end(+who: Nat, +to: Nat, +a0: Nat, +a1: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    Pair.sync()
    Evm.emit(Pair.Burn(who, to, a0, a1))

def end.second(+rest: List<&2, Calls.Step>, +who: Nat, +to: Nat, +a0: Nat, +a1: Nat, +c0: Nat, +st: List<&2, Evm.Slot>, +ca: Nat,
  +li: Nat, +lo: List<&2, Evm.Log>, +facts: List<&2, Evm.Fact>, +readings: List<&2, Nat>, +self: Nat, +hashes: List<&2, Evm.Hashed>,
  +signers: List<&2, Evm.Signed>, answers: List<&2, Evm.Answer>, -l: Nat, -s: Nat, -b0: Nat, -b1: Nat,
  +f: {True{} == Laws.within(l, s, b0, b1, [a0, a1]) : Bool}) ->
  {True{} == Laws.paid(l, s, b0, b1, closed(rest, Evm.answer(Unit, balance.of(st, 4n, self),
    c1 => v => burn.fin(who, to, a0, a1, c0, c1)(Unit, ok(Unit), v),
    Evm.State{st, ca, li, lo, Evm.World{facts, readings, self, hashes, signers, answers}}))) : Bool}:
  match answers:
    case Nil{}:
      closed_revert(rest, pays(l, s, b0, b1), {==})
    case Evm.Answer{+q, +c1} <> +more:
      closed_pick(rest, Evm.same.call(q, balance.of(st, 4n, self)),
        burn.fin(who, to, a0, a1, c0, c1)(Unit, ok(Unit), Evm.State{st, ca, li, lo, Evm.World{facts, readings, self, hashes, signers, more}}),
        Evm.Revert{}, pays(l, s, b0, b1),
        _ => closed_ok(rest, Evm.State{Evm.Slot{Evm.Plain{6n}, c1} <> Evm.Slot{Evm.Plain{5n}, c0} <> st, ca, li,
          Pair.Burn(who, to, a0, a1) <> Pair.Sync(c0, c1) <> lo, Evm.World{facts, readings, self, hashes, signers, more}}, pays(l, s, b0, b1), f),
        _ => closed_revert(rest, pays(l, s, b0, b1), {==}))

# The end from any state that the callbacks leave.
def end.first(+rest: List<&2, Calls.Step>, +who: Nat, +to: Nat, +a0: Nat, +a1: Nat, u: Evm.State, -l: Nat, -s: Nat, -b0: Nat, -b1: Nat,
  +f: {True{} == Laws.within(l, s, b0, b1, [a0, a1]) : Bool}) ->
  {True{} == Laws.paid(l, s, b0, b1, closed(rest, burn.end(who, to, a0, a1)(Unit, ok(Unit), u))) : Bool}:
  match u:
    case Evm.State{+st, +ca, +li, +lo, Evm.World{+facts, +readings, +self, +hashes, +signers, answers}}:
      match answers:
        case Nil{}:
          closed_revert(rest, pays(l, s, b0, b1), {==})
        case Evm.Answer{+q, +c0} <> +more:
          closed_pick(rest, Evm.same.call(q, balance.of(st, 3n, self)),
            Evm.answer(Unit, balance.of(st, 4n, self), c1 => v => burn.fin(who, to, a0, a1, c0, c1)(Unit, ok(Unit), v),
              Evm.State{st, ca, li, lo, Evm.World{facts, readings, self, hashes, signers, more}}),
            Evm.Revert{}, pays(l, s, b0, b1),
            _ => end.second(rest, who, to, a0, a1, c0, st, ca, li, lo, facts, readings, self, hashes, signers, more, l, s, b0, b1, f),
            _ => closed_revert(rest, pays(l, s, b0, b1), {==}))

def burn.after1(+who: Nat, +to: Nat, +a0: Nat, +a1: Nat) -> Nat -> Evm.State -> Evm.Outcome<Unit>:
  x => u => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n), burn.end(who, to, a0, a1)(Unit, ok(Unit), u),
    Evm.Raise{Pair.TransferFailed()})

def burn.after0(+who: Nat, +to: Nat, +a0: Nat, +a1: Nat, +t1: Nat) -> Nat -> Evm.State -> Evm.Outcome<Unit>:
  x => u => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n),
    Pair.pay(t1, to, a1)(Unit, v => w => burn.end(who, to, a0, a1)(Unit, ok(Unit), w), u), Evm.Raise{Pair.TransferFailed()})

def burn.paid1(+x: Nat, +rest: List<&2, Calls.Step>, u: Evm.State, +who: Nat, +to: Nat, +a0: Nat, +a1: Nat,
  -l: Nat, -s: Nat, -b0: Nat, -b1: Nat, +f: {True{} == Laws.within(l, s, b0, b1, [a0, a1]) : Bool}) ->
  {True{} == Laws.paid(l, s, b0, b1, closed(rest, burn.after1(who, to, a0, a1)(x, u))) : Bool}:
  closed_pick(rest, Nat.is_eq(x, 1n), burn.end(who, to, a0, a1)(Unit, ok(Unit), u), Evm.Raise{Pair.TransferFailed()},
    pays(l, s, b0, b1),
    _ => end.first(rest, who, to, a0, a1, u, l, s, b0, b1, f),
    _ => closed_raise(rest, Pair.TransferFailed(), pays(l, s, b0, b1), {==}))

def burn.paid0(+x: Nat, +rest: List<&2, Calls.Step>, +u: Evm.State, +who: Nat, +to: Nat, +a0: Nat, +a1: Nat, +t1: Nat,
  -l: Nat, -s: Nat, -b0: Nat, -b1: Nat, +f: {True{} == Laws.within(l, s, b0, b1, [a0, a1]) : Bool}) ->
  {True{} == Laws.paid(l, s, b0, b1, closed(rest, burn.after0(who, to, a0, a1, t1)(x, u))) : Bool}:
  closed_pick(rest, Nat.is_eq(x, 1n), Pair.pay(t1, to, a1)(Unit, v => w => burn.end(who, to, a0, a1)(Unit, ok(Unit), w), u),
    Evm.Raise{Pair.TransferFailed()}, pays(l, s, b0, b1),
    _ => calling(rest, Evm.Call{t1, "transfer", [to, a1]}, u, burn.after1(who, to, a0, a1), pays(l, s, b0, b1), {==},
      y => more => v => burn.paid1(y, more, v, who, to, a0, a1, l, s, b0, b1, f)),
    _ => closed_raise(rest, Pair.TransferFailed(), pays(l, s, b0, b1), {==}))

# The liquidity that the pair holds, and the amounts that it pays for it.
def held(+st: List<&2, Evm.Slot>, +self: Nat) -> Nat:
  Evm.lookup(st, Evm.Mapped{Evm.Plain{1n}, self})

def owed(+st: List<&2, Evm.Slot>, +self: Nat, +b: Nat) -> Nat:
  Nat.div(Nat.mul(held(st, self), b), at(st, 0n))

# A burn with its checks as parameters, up to the first call.
def burn.go(steps: List<&2, Calls.Step>, +st: List<&2, Evm.Slot>, +ca: Nat, +li: Nat, +lo: List<&2, Evm.Log>, +facts: List<&2, Evm.Fact>,
  +readings: List<&2, Nat>, +self: Nat, +hashes: List<&2, Evm.Hashed>, +signers: List<&2, Evm.Signed>, +more: List<&2, Evm.Answer>,
  +to: Nat, +b0: Nat, +b1: Nat, cv0: Bool, cv1: Bool, cx: Bool, cd: Bool, +ed: {cd == Nat.is_eq(at(st, 0n), 0n) : Bool},
  cy: Bool, cd2: Bool, c0: Bool, c1: Bool, cb: Bool, cs: Bool) ->
  {True{} == Laws.paid(held(st, self), at(st, 0n), b0, b1, closed(steps,
    Bool.pick(Evm.Outcome<Unit>, cv0,
    Bool.pick(Evm.Outcome<Unit>, cv1,
    Bool.pick(Evm.Outcome<Unit>, cx,
    Bool.pick(Evm.Outcome<Unit>, cd, Evm.Revert{},
    Bool.pick(Evm.Outcome<Unit>, cy,
    Bool.pick(Evm.Outcome<Unit>, cd2, Evm.Revert{},
    Bool.pick(Evm.Outcome<Unit>, c0,
    Bool.pick(Evm.Outcome<Unit>, c1,
    Bool.pick(Evm.Outcome<Unit>, cb, Evm.Revert{},
    Bool.pick(Evm.Outcome<Unit>, cs, Evm.Revert{},
      Evm.Calling{Evm.Call{at(st, 3n), "transfer", [to, owed(st, self, b0)]},
        Evm.State{Evm.Slot{Evm.Plain{0n}, Nat.sub(at(st, 0n), held(st, self))}
          <> Evm.Slot{Evm.Mapped{Evm.Plain{1n}, self}, Nat.sub(held(st, self), held(st, self))} <> st, ca, li,
          Evm.Log{"Transfer", [self, 0n], [held(st, self)]} <> lo, Evm.World{facts, readings, self, hashes, signers, more}},
        burn.after0(ca, to, owed(st, self, b0), owed(st, self, b1), at(st, 4n))})),
      Evm.Raise{Pair.InsufficientLiquidityBurned()}),
      Evm.Raise{Pair.InsufficientLiquidityBurned()})),
      Evm.Revert{})),
      Evm.Revert{}),
      Evm.Revert{}),
      Evm.Revert{}))) : Bool}:
  match cv0:
    case False{}:
      closed_revert(steps, pays(held(st, self), at(st, 0n), b0, b1), {==})
    case True{}:
      match cv1:
        case False{}:
          closed_revert(steps, pays(held(st, self), at(st, 0n), b0, b1), {==})
        case True{}:
          match cx:
            case False{}:
              closed_revert(steps, pays(held(st, self), at(st, 0n), b0, b1), {==})
            case True{}:
              match cd:
                case True{}:
                  closed_revert(steps, pays(held(st, self), at(st, 0n), b0, b1), {==})
                case False{}:
                  match cy:
                    case False{}:
                      closed_revert(steps, pays(held(st, self), at(st, 0n), b0, b1), {==})
                    case True{}:
                      match cd2:
                        case True{}:
                          closed_revert(steps, pays(held(st, self), at(st, 0n), b0, b1), {==})
                        case False{}:
                          match c0:
                            case False{}:
                              closed_raise(steps, Pair.InsufficientLiquidityBurned(), pays(held(st, self), at(st, 0n), b0, b1), {==})
                            case True{}:
                              match c1:
                                case False{}:
                                  closed_raise(steps, Pair.InsufficientLiquidityBurned(), pays(held(st, self), at(st, 0n), b0, b1), {==})
                                case True{}:
                                  match cb:
                                    case True{}:
                                      closed_revert(steps, pays(held(st, self), at(st, 0n), b0, b1), {==})
                                    case False{}:
                                      match cs:
                                        case True{}:
                                          closed_revert(steps, pays(held(st, self), at(st, 0n), b0, b1), {==})
                                        case False{}:
                                          calling(steps, Evm.Call{at(st, 3n), "transfer", [to, owed(st, self, b0)]},
                                            Evm.State{Evm.Slot{Evm.Plain{0n}, Nat.sub(at(st, 0n), held(st, self))}
                                              <> Evm.Slot{Evm.Mapped{Evm.Plain{1n}, self}, Nat.sub(held(st, self), held(st, self))} <> st, ca, li,
                                              Evm.Log{"Transfer", [self, 0n], [held(st, self)]} <> lo, Evm.World{facts, readings, self, hashes, signers, more}},
                                            burn.after0(ca, to, owed(st, self, b0), owed(st, self, b1), at(st, 4n)),
                                            pays(held(st, self), at(st, 0n), b0, b1), {==},
                                            x => rest => u => burn.paid0(x, rest, u, ca, to, owed(st, self, b0), owed(st, self, b1), at(st, 4n),
                                              held(st, self), at(st, 0n), b0, b1,
                                              both(Nat.is_lt(Nat.mul(held(st, self), b0), Nat.mul(owed(st, self, b0), at(st, 0n))),
                                                Nat.is_lt(Nat.mul(held(st, self), b1), Nat.mul(owed(st, self, b1), at(st, 0n))),
                                                part_le(Nat.mul(held(st, self), b0), at(st, 0n), ed),
                                                part_le(Nat.mul(held(st, self), b1), at(st, 0n), ed))))

def Laws.burn(steps, storage, caller, limit, logs, facts, readings, self, hashes, signers, q0, b0, q1, b1, more, to):
  burn.go(steps, storage, caller, limit, logs, facts, readings, self, hashes, signers, more, to, b0, b1,
    Evm.same.call(q0, balance.of(storage, 3n, self)), Evm.same.call(q1, balance.of(storage, 4n, self)),
    Nat.is_lt(Nat.mul(held(storage, self), b0), limit), Nat.is_eq(at(storage, 0n), 0n), {==},
    Nat.is_lt(Nat.mul(held(storage, self), b1), limit), Nat.is_eq(at(storage, 0n), 0n),
    Nat.is_lt(0n, owed(storage, self, b0)), Nat.is_lt(0n, owed(storage, self, b1)),
    Nat.is_lt(held(storage, self), held(storage, self)), Nat.is_lt(at(storage, 0n), held(storage, self)))
