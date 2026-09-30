import Base
import ../../src/Evm.bend as Evm
import ../../src/calls.bend as Calls
import ../../src/nat.bend as N
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

def ok() -> Unit -> Evm.State -> Evm.Outcome<Unit>:
  x => t => Evm.Ok{x, t}

def closed(steps: List<&2, Calls.Step>, o: Evm.Outcome<Unit>) -> Evm.Outcome<Unit>:
  Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, False{}, o)

def opened(steps: List<&2, Calls.Step>, s: Evm.State) -> Evm.Outcome<Unit>:
  Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, True{}, Evm.Ok{Unit{}, s})

def closed_revert(steps: List<&2, Calls.Step>, -k: Nat) -> {True{} == Laws.kept(k, closed(steps, Evm.Revert{})) : Bool}:
  match steps:
    case Nil{}:
      {==}
    case step <> _:
      match step:
        case Calls.Enter{_, _, _, _}:
          {==}
        case Calls.Answer{_, _, _}:
          {==}

def closed_raise(steps: List<&2, Calls.Step>, -e: Evm.Error, -k: Nat) ->
  {True{} == Laws.kept(k, closed(steps, Evm.Raise{e})) : Bool}:
  match steps:
    case Nil{}:
      {==}
    case step <> _:
      match step:
        case Calls.Enter{_, _, _, _}:
          {==}
        case Calls.Answer{_, _, _}:
          {==}

def closed_ok(steps: List<&2, Calls.Step>, -t: Evm.State, -k: Nat, h: {True{} == Laws.kept(k, Evm.Ok{Unit{}, t}) : Bool}) ->
  {True{} == Laws.kept(k, closed(steps, Evm.Ok{Unit{}, t})) : Bool}:
  match steps:
    case Nil{}:
      h
    case step <> _:
      match step:
        case Calls.Enter{_, _, _, _}:
          h
        case Calls.Answer{_, _, _}:
          h

def pick_keep(+b: Bool, -x: Evm.Outcome<Unit>, -y: Evm.Outcome<Unit>, -k: Nat,
  hx: {True{} == b : Bool} -> {True{} == Laws.kept(k, x) : Bool},
  hy: {False{} == b : Bool} -> {True{} == Laws.kept(k, y) : Bool}) ->
  {True{} == Laws.kept(k, Bool.pick(Evm.Outcome<Unit>, b, x, y)) : Bool}:
  match b:
    case True{}:
      hx({==})
    case False{}:
      hy({==})

def closed_pick(-steps: List<&2, Calls.Step>, +b: Bool, -x: Evm.Outcome<Unit>, -y: Evm.Outcome<Unit>, -k: Nat,
  hx: {True{} == b : Bool} -> {True{} == Laws.kept(k, closed(steps, x)) : Bool},
  hy: {False{} == b : Bool} -> {True{} == Laws.kept(k, closed(steps, y)) : Bool}) ->
  {True{} == Laws.kept(k, closed(steps, Bool.pick(Evm.Outcome<Unit>, b, x, y))) : Bool}:
  match b:
    case True{}:
      hx({==})
    case False{}:
      hy({==})

# A call keeps the bound when the rest of the run keeps it from any state:
# the answer's callbacks may leave any state.
def calling(inner: List<&2, Calls.Step>, +c: Evm.Call, +t: Evm.State, -r: Nat -> Evm.State -> Evm.Outcome<Unit>, -k: Nat,
  hr: @x: Nat -> @rest: List<&2, Calls.Step> -> @u: Evm.State -> {True{} == Laws.kept(k, closed(rest, r(x, u))) : Bool}) ->
  {True{} == Laws.kept(k, closed(inner, Evm.Calling{c, t, r})) : Bool}:
  match inner:
    case Nil{}:
      {==}
    case step <> +rest:
      match step:
        case Calls.Enter{_, _, _, _}:
          {==}
        case Calls.Answer{+q, +cbs, +x}:
          pick_keep(Evm.same.call(q, c), closed(rest, r(x, Calls.after(Unit, t, opened(cbs, t)))), Evm.Revert{}, k,
            _ => hr(x, rest, Calls.after(Unit, t, opened(cbs, t))), _ => {==})

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
      closed_revert(rest, Nat.mul(r0, r1))
    case False{}:
      match cl1:
        case True{}:
          closed_revert(rest, Nat.mul(r0, r1))
        case False{}:
          match cin:
            case False{}:
              closed_raise(rest, Pair.InsufficientInputAmount(), Nat.mul(r0, r1))
            case True{}:
              match cm0:
                case False{}:
                  closed_revert(rest, Nat.mul(r0, r1))
                case True{}:
                  match cf0:
                    case False{}:
                      closed_revert(rest, Nat.mul(r0, r1))
                    case True{}:
                      match ca0:
                        case True{}:
                          closed_revert(rest, Nat.mul(r0, r1))
                        case False{}:
                          match cm1:
                            case False{}:
                              closed_revert(rest, Nat.mul(r0, r1))
                            case True{}:
                              match cf1:
                                case False{}:
                                  closed_revert(rest, Nat.mul(r0, r1))
                                case True{}:
                                  match ca1:
                                    case True{}:
                                      closed_revert(rest, Nat.mul(r0, r1))
                                    case False{}:
                                      match cA:
                                        case False{}:
                                          closed_revert(rest, Nat.mul(r0, r1))
                                        case True{}:
                                          match cB:
                                            case False{}:
                                              closed_revert(rest, Nat.mul(r0, r1))
                                            case True{}:
                                              match cS:
                                                case False{}:
                                                  closed_revert(rest, Nat.mul(r0, r1))
                                                case True{}:
                                                  match cL:
                                                    case False{}:
                                                      closed_revert(rest, Nat.mul(r0, r1))
                                                    case True{}:
                                                      match cK:
                                                        case False{}:
                                                          closed_raise(rest, Pair.K(), Nat.mul(r0, r1))
                                                        case True{}:
                                                          closed_ok(rest, Evm.State{Evm.Slot{Evm.Plain{6n}, b1} <> Evm.Slot{Evm.Plain{5n}, b0} <> st,
                                                            ca, li, Evm.Log{"Swap", [who, to], [i0, i1, out0, out1]} <> Evm.Log{"Sync", [], [b0, b1]} <> lo, w},
                                                            Nat.mul(r0, r1), bound(b0, b1, Nat.mul(i0, 3n), Nat.mul(i1, 3n), r0, r1, eK))

# The amount in of one token: its balance above the reserve left after
# the amount out.
def into(+r: Nat, +out: Nat, +b: Nat, +li: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(Nat.sub(r, out), b), Evm.op(Evm.Sub{}, [b, Nat.sub(r, out)], li), 0n)

def check.at(rest: List<&2, Calls.Step>, +who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat, +b0: Nat,
  +b1: Nat, +st: List<&2, Evm.Slot>, +ca: Nat, +li: Nat, +lo: List<&2, Evm.Log>, +w: Evm.World) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest,
    Pair.check(who, to, out0, out1, r0, r1, b0, b1)(Unit, ok(), Evm.State{st, ca, li, lo, w}))) : Bool}:
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
  +st: List<&2, Evm.Slot>, +ca: Nat, +li: Nat, +lo: List<&2, Evm.Log>, +time: Nat, +chain: Nat, +self: Nat,
  +hashes: List<&2, Evm.Hashed>, +signers: List<&2, Evm.Signed>, answers: List<&2, Evm.Answer>) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest, Evm.answer(Unit, balance.of(st, 4n, self),
    b1 => v => Pair.check(who, to, out0, out1, r0, r1, b0, b1)(Unit, ok(), v),
    Evm.State{st, ca, li, lo, Evm.World{time, chain, self, hashes, signers, answers}}))) : Bool}:
  match answers:
    case Nil{}:
      closed_revert(rest, Nat.mul(r0, r1))
    case Evm.Answer{+q, +b1} <> +more:
      closed_pick(rest, Evm.same.call(q, balance.of(st, 4n, self)),
        Pair.check(who, to, out0, out1, r0, r1, b0, b1)(Unit, ok(),
          Evm.State{st, ca, li, lo, Evm.World{time, chain, self, hashes, signers, more}}),
        Evm.Revert{}, Nat.mul(r0, r1),
        _ => check.at(rest, who, to, out0, out1, r0, r1, b0, b1, st, ca, li, lo, Evm.World{time, chain, self, hashes, signers, more}),
        _ => closed_revert(rest, Nat.mul(r0, r1)))

# settle from any state: the callbacks may leave any storage and answers.
def settled(+rest: List<&2, Calls.Step>, +who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat, u: Evm.State) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest, Pair.settle(who, to, out0, out1, r0, r1)(Unit, ok(), u))) : Bool}:
  match u:
    case Evm.State{+st, +ca, +li, +lo, Evm.World{+time, +chain, +self, +hashes, +signers, answers}}:
      match answers:
        case Nil{}:
          closed_revert(rest, Nat.mul(r0, r1))
        case Evm.Answer{+q, +b0} <> +more:
          closed_pick(rest, Evm.same.call(q, balance.of(st, 3n, self)),
            Evm.answer(Unit, balance.of(st, 4n, self), b1 => v => Pair.check(who, to, out0, out1, r0, r1, b0, b1)(Unit, ok(), v),
              Evm.State{st, ca, li, lo, Evm.World{time, chain, self, hashes, signers, more}}),
            Evm.Revert{}, Nat.mul(r0, r1),
            _ => viewed(rest, who, to, out0, out1, r0, r1, b0, st, ca, li, lo, time, chain, self, hashes, signers, more),
            _ => closed_revert(rest, Nat.mul(r0, r1)))

# After the second call: the token must return 1.
def paid1(+x: Nat, +rest: List<&2, Calls.Step>, u: Evm.State, +who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest, Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n),
    Pair.settle(who, to, out0, out1, r0, r1)(Unit, ok(), u), Evm.Raise{Pair.TransferFailed()}))) : Bool}:
  closed_pick(rest, Nat.is_eq(x, 1n), Pair.settle(who, to, out0, out1, r0, r1)(Unit, ok(), u), Evm.Raise{Pair.TransferFailed()},
    Nat.mul(r0, r1),
    _ => settled(rest, who, to, out0, out1, r0, r1, u),
    _ => closed_raise(rest, Pair.TransferFailed(), Nat.mul(r0, r1)))

def after1(+who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat) -> Nat -> Evm.State -> Evm.Outcome<Unit>:
  x => u => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n), Pair.settle(who, to, out0, out1, r0, r1)(Unit, ok(), u),
    Evm.Raise{Pair.TransferFailed()})

# After the first call: the token must return 1, then the second call.
def paid0(+x: Nat, +rest: List<&2, Calls.Step>, +u: Evm.State, +who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat,
  +t1: Nat) ->
  {True{} == Laws.kept(Nat.mul(r0, r1), closed(rest, Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n),
    Pair.pay(t1, to, out1)(Unit, v => w => Pair.settle(who, to, out0, out1, r0, r1)(Unit, ok(), w), u),
    Evm.Raise{Pair.TransferFailed()}))) : Bool}:
  closed_pick(rest, Nat.is_eq(x, 1n), Pair.pay(t1, to, out1)(Unit, v => w => Pair.settle(who, to, out0, out1, r0, r1)(Unit, ok(), w), u),
    Evm.Raise{Pair.TransferFailed()}, Nat.mul(r0, r1),
    _ => calling(rest, Evm.Call{t1, "transfer", [to, out1]}, u, after1(who, to, out0, out1, r0, r1), Nat.mul(r0, r1),
      y => more => v => paid1(y, more, v, who, to, out0, out1, r0, r1)),
    _ => closed_raise(rest, Pair.TransferFailed(), Nat.mul(r0, r1)))

def after0(+who: Nat, +to: Nat, +out0: Nat, +out1: Nat, +r0: Nat, +r1: Nat, +t1: Nat) -> Nat -> Evm.State -> Evm.Outcome<Unit>:
  x => u => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n),
    Pair.pay(t1, to, out1)(Unit, v => w => Pair.settle(who, to, out0, out1, r0, r1)(Unit, ok(), w), u),
    Evm.Raise{Pair.TransferFailed()})

# The checks before the first call, then the call.
def top(steps: List<&2, Calls.Step>, +st: List<&2, Evm.Slot>, +ca: Nat, +li: Nat, +lo: List<&2, Evm.Log>, +w: Evm.World,
  +out0: Nat, +out1: Nat, +to: Nat, c1: Bool, c2: Bool, c3: Bool, c4: Bool, c5: Bool) ->
  {True{} == Laws.kept(Nat.mul(at(st, 5n), at(st, 6n)), closed(steps,
    Bool.pick(Evm.Outcome<Unit>, c1,
    Bool.pick(Evm.Outcome<Unit>, c2,
    Bool.pick(Evm.Outcome<Unit>, c3,
    Bool.pick(Evm.Outcome<Unit>, c4,
    Bool.pick(Evm.Outcome<Unit>, c5,
      Evm.Calling{Evm.Call{at(st, 3n), "transfer", [to, out0]}, Evm.State{st, ca, li, lo, w},
        after0(ca, to, out0, out1, at(st, 5n), at(st, 6n), at(st, 4n))},
      Evm.Raise{Pair.InvalidTo()}), Evm.Raise{Pair.InvalidTo()}),
      Evm.Raise{Pair.InsufficientLiquidity()}), Evm.Raise{Pair.InsufficientLiquidity()}),
      Evm.Raise{Pair.InsufficientOutputAmount()}))) : Bool}:
  match c1:
    case False{}:
      closed_raise(steps, Pair.InsufficientOutputAmount(), Nat.mul(at(st, 5n), at(st, 6n)))
    case True{}:
      match c2:
        case False{}:
          closed_raise(steps, Pair.InsufficientLiquidity(), Nat.mul(at(st, 5n), at(st, 6n)))
        case True{}:
          match c3:
            case False{}:
              closed_raise(steps, Pair.InsufficientLiquidity(), Nat.mul(at(st, 5n), at(st, 6n)))
            case True{}:
              match c4:
                case False{}:
                  closed_raise(steps, Pair.InvalidTo(), Nat.mul(at(st, 5n), at(st, 6n)))
                case True{}:
                  match c5:
                    case False{}:
                      closed_raise(steps, Pair.InvalidTo(), Nat.mul(at(st, 5n), at(st, 6n)))
                    case True{}:
                      calling(steps, Evm.Call{at(st, 3n), "transfer", [to, out0]}, Evm.State{st, ca, li, lo, w},
                        after0(ca, to, out0, out1, at(st, 5n), at(st, 6n), at(st, 4n)), Nat.mul(at(st, 5n), at(st, 6n)),
                        x => rest => u => paid0(x, rest, u, ca, to, out0, out1, at(st, 5n), at(st, 6n), at(st, 4n)))

def Laws.swap(steps, s, amount0Out, amount1Out, to):
  match s:
    case Evm.State{+st, +ca, +li, +lo, +w}:
      top(steps, st, ca, li, lo, w, amount0Out, amount1Out, to,
        Nat.is_lt(0n, Evm.op(Evm.Or{}, [amount0Out, amount1Out], li)), Nat.is_lt(amount0Out, at(st, 5n)),
        Nat.is_lt(amount1Out, at(st, 6n)), Bool.not(Nat.is_eq(to, at(st, 3n))), Bool.not(Nat.is_eq(to, at(st, 4n))))
