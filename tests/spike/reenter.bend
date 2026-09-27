import Base
import ../../src/Evm.bend as Evm
import ../../src/nat.bend as N

# Spike: a model of calls that write, with reentrancy. A call stops the
# contract; the run then takes the next answer, runs the callbacks that it
# lists (calls from the callee into our own entries, each with its own
# answers), and gives the returned word to the rest of the contract.
#
# It shows three kinds of law about pay, which calls out after it updates:
# with no callbacks (exact, by {==}); with any callbacks (composition, by
# {==}); and a rule that holds for every callee (by induction on the
# answers). bad calls between its updates, and one callback breaks the rule.

type Out<-A: Data> is Type:
  Ok{value: A, state: Evm.State}
  Revert{}
  Raise{error: Evm.Error}
  Calling{call: Evm.Call, state: Evm.State, resume: Nat -> Evm.State -> Out<A>}

# An answer to a call: the callbacks during it, then the returned word. A
# callback: its sender, the entry's index, the argument words and the
# answers to the calls that the entry makes.
type Step is Data:
  Answer{call: Evm.Call, callbacks: List<&2, Step>, value: Nat}
  Enter{sender: Nat, entry: Nat, args: List<&2, Nat>, answers: List<&2, Step>}

def Con(-A: Data) -> Type:
  @-R: Data -> @k: (A -> Evm.State -> Out<R>) -> Evm.State -> Out<R>

def Con.pure(-A: Data, x: A) -> Con(A):
  R => k => s => k(x, s)

def Con.bind(-A: Data, -B: Data, m: Con(A), f: A -> Con(B)) -> Con(B):
  R => k => m(R, x => f(x, R, k))

def sload(+slot: Nat) -> Con(Nat):
  R => k => +s => k(Evm.lookup(Evm.storage.of(s), Evm.Plain{slot}), s)

def sstore(slot: Nat, value: Nat) -> Con(Unit):
  R => k => s => k(Unit{}, Evm.write.go(Evm.Plain{slot}, value, s))

def require(ok: Bool) -> Con(Unit):
  R => k => s => Bool.pick(Out<R>, ok, k(Unit{}, s), Revert{})

def revert() -> Con(Unit):
  R => k => s => Revert{}

def call(c: Evm.Call) -> Con(Nat):
  R => k => s => Calling{c, s, k}

def with.caller(who: Nat, s: Evm.State) -> Evm.State:
  match s:
    case Evm.State{storage, _, limit, logs, world}:
      Evm.State{storage, who, limit, logs, world}

# The state after the callbacks of an answer.
def after(-A: Data, s: Evm.State, o: Out<A>) -> Evm.State:
  match o:
    case Ok{_, t}:
      t
    case Revert{}:
      s
    case Raise{_}:
      s
    case Calling{_, _, _}:
      s

# The state after one callback: its state with our caller back, or the old
# state if it reverted, as the callee may catch that.
def back(-A: Data, +s: Evm.State, o: Out<A>) -> Evm.State:
  match o:
    case Ok{_, t}:
      with.caller(Evm.caller.of(s), t)
    case Revert{}:
      s
    case Raise{_}:
      s
    case Calling{_, _, _}:
      s

def Table() -> Type:
  Nat -> List<&2, Nat> -> Con(Unit)

# The end of a run: a call with no answer reverts.
def stop(-A: Data, o: Out<A>) -> Out<A>:
  match o:
    case Ok{v, s}:
      Ok{v, s}
    case Revert{}:
      Revert{}
    case Raise{e}:
      Raise{e}
    case Calling{_, _, _}:
      Revert{}

# Runs an outcome with the steps. open: the steps are callbacks that run
# after o; otherwise they only answer o's calls. The table is a template, as
# a function cannot be copied.
def drive(~table: Table, steps: List<&2, Step>, -A: Data, open: Bool, o: Out<A>) -> Out<A>:
  match steps:
    case Nil{}:
      stop(A, o)
    case step <> rest:
      match step:
        case Enter{sender, entry, args, inner}:
          match open:
            case True{}:
              match o:
                case Ok{v, +s}:
                  +t = back(Unit, s, drive(~table, inner, Unit, False{}, table(entry, args, Unit, u => w => Ok{u, w}, with.caller(sender, s))))
                  drive(~table, rest, A, True{}, Ok{v, t})
                case Revert{}:
                  Revert{}
                case Raise{e}:
                  Raise{e}
                case Calling{_, _, _}:
                  Revert{}
            case False{}:
              stop(A, o)
        case Answer{q, cbs, x}:
          match open:
            case True{}:
              stop(A, o)
            case False{}:
              match o:
                case Ok{v, s}:
                  Ok{v, s}
                case Revert{}:
                  Revert{}
                case Raise{e}:
                  Raise{e}
                case Calling{c, +s, r}:
                  Bool.pick(Out<A>, Evm.same.call(q, c),
                    drive(~table, rest, A, False{}, r(x, after(Unit, s, drive(~table, cbs, Unit, True{}, Ok{Unit{}, s})))),
                    Revert{})

def exec(~table: Table, -A: Data, m: Con(A), steps: List<&2, Step>, s: Evm.State) -> Out<A>:
  drive(~table, steps, A, False{}, m(A, x => t => Ok{x, t}, s))

# ---- the contract: slots 0 and 1 must stay equal ----

def bump(+v: Nat) -> Con(Unit):
  do Con<Unit>:
    a : Nat <- sload(0n)
    b : Nat <- sload(1n)
    sstore(0n, Nat.add(a, v))
    sstore(1n, Nat.add(b, v))

# Updates both slots, then calls: callbacks see a good state.
def pay(+to: Nat, +v: Nat) -> Con(Unit):
  do Con<Unit>:
    a : Nat <- sload(0n)
    b : Nat <- sload(1n)
    sstore(0n, Nat.add(a, v))
    sstore(1n, Nat.add(b, v))
    ok : Nat <- call(Evm.Call{to, "pay", [v]})
    require(Nat.is_eq(ok, 1n))

# Calls between the two updates: callbacks see a bad state, and b is stale
# after the call.
def bad(+to: Nat, +v: Nat) -> Con(Unit):
  do Con<Unit>:
    a : Nat <- sload(0n)
    b : Nat <- sload(1n)
    sstore(0n, Nat.add(a, v))
    ok : Nat <- call(Evm.Call{to, "pay", [v]})
    sstore(1n, Nat.add(b, v))
    require(Nat.is_eq(ok, 1n))

def good(i: Nat, args: List<&2, Nat>) -> Con(Unit):
  match i:
    case 0n:
      match args:
        case Nil{}:
          revert()
        case v <> _:
          bump(v)
    case 1n+j:
      match j:
        case 0n:
          match args:
            case Nil{}:
              revert()
            case to <> more:
              match more:
                case Nil{}:
                  revert()
                case v <> _:
                  pay(to, v)
        case 1n+_:
          revert()

def worse(i: Nat, args: List<&2, Nat>) -> Con(Unit):
  match i:
    case 0n:
      match args:
        case Nil{}:
          revert()
        case v <> _:
          bump(v)
    case 1n+j:
      match j:
        case 0n:
          match args:
            case Nil{}:
              revert()
            case to <> more:
              match more:
                case Nil{}:
                  revert()
                case v <> _:
                  bad(to, v)
        case 1n+_:
          revert()

# ---- kind 1: no callbacks, an exact law by {==} ----

def no_callbacks(storage: List<&2, Evm.Slot>, who: Nat, limit: Nat, logs: List<&2, Evm.Log>, world: Evm.World,
  q: Evm.Call, +to: Nat, +v: Nat) ->
  {exec(~good, Unit, pay(to, v), [Answer{q, [], 1n}], Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Out<Unit>, Evm.same.call(q, Evm.Call{to, "pay", [v]}),
      Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{1n}, Nat.add(Evm.lookup(storage, Evm.Plain{1n}), v)} <> Evm.Slot{Evm.Plain{0n}, Nat.add(Evm.lookup(storage, Evm.Plain{0n}), v)} <> storage, who, limit, logs, world}},
      Revert{}) : Out<Unit>}:
  {==}

# ---- kind 2: any callbacks, the composition law by {==} ----

def composed(storage: List<&2, Evm.Slot>, who: Nat, limit: Nat, logs: List<&2, Evm.Log>, world: Evm.World,
  q: Evm.Call, cbs: List<&2, Step>, +to: Nat, +v: Nat) ->
  {exec(~good, Unit, pay(to, v), [Answer{q, cbs, 1n}], Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Out<Unit>, Evm.same.call(q, Evm.Call{to, "pay", [v]}),
      Ok{Unit{}, after(Unit, Evm.State{Evm.Slot{Evm.Plain{1n}, Nat.add(Evm.lookup(storage, Evm.Plain{1n}), v)} <> Evm.Slot{Evm.Plain{0n}, Nat.add(Evm.lookup(storage, Evm.Plain{0n}), v)} <> storage, who, limit, logs, world},
        drive(~good, cbs, Unit, True{},
          Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{1n}, Nat.add(Evm.lookup(storage, Evm.Plain{1n}), v)} <> Evm.Slot{Evm.Plain{0n}, Nat.add(Evm.lookup(storage, Evm.Plain{0n}), v)} <> storage, who, limit, logs, world}}))},
      Revert{}) : Out<Unit>}:
  {==}

# ---- the bad order: one callback breaks the rule ----

def broken(who: Nat, limit: Nat, logs: List<&2, Evm.Log>, world: Evm.World, q: Evm.Call, +to: Nat) ->
  {exec(~worse, Unit, bad(to, 5n), [Answer{q, [Enter{7n, 0n, [9n], []}], 1n}], Evm.State{[], who, limit, logs, world})
    == Bool.pick(Out<Unit>, Evm.same.call(q, Evm.Call{to, "pay", [5n]}),
      Ok{Unit{}, Evm.State{[Evm.Slot{Evm.Plain{1n}, 5n}, Evm.Slot{Evm.Plain{1n}, 9n}, Evm.Slot{Evm.Plain{0n}, 14n}, Evm.Slot{Evm.Plain{0n}, 5n}],
        who, limit, logs, world}},
      Revert{}) : Out<Unit>}:
  {==}

# ---- kind 3: the rule holds after pay, for any callee ----

def inv(s: Evm.State) -> Bool:
  match s:
    case Evm.State{+storage, _, _, _, _}:
      Nat.is_eq(Evm.lookup(storage, Evm.Plain{0n}), Evm.lookup(storage, Evm.Plain{1n}))

def holds(-A: Data, o: Out<A>) -> Bool:
  match o:
    case Ok{_, t}:
      inv(t)
    case Revert{}:
      True{}
    case Raise{_}:
      True{}
    case Calling{_, _, _}:
      False{}

def after_keep(-A: Data, +s: Evm.State, o: Out<A>, hs: {True{} == inv(s) : Bool}, ho: {True{} == holds(A, o) : Bool}) ->
  {True{} == inv(after(A, s, o)) : Bool}:
  match o:
    case Ok{_, _}:
      ho
    case Revert{}:
      hs
    case Raise{_}:
      hs
    case Calling{_, _, _}:
      hs

def back_keep(-A: Data, +s: Evm.State, o: Out<A>, hs: {True{} == inv(s) : Bool}, ho: {True{} == holds(A, o) : Bool}) ->
  {True{} == inv(back(A, s, o)) : Bool}:
  match o:
    case Ok{_, t}:
      match t:
        case Evm.State{_, _, _, _, _}:
          ho
    case Revert{}:
      hs
    case Raise{_}:
      hs
    case Calling{_, _, _}:
      hs

def pick_keep(-A: Data, +b: Bool, -x: Out<A>, -y: Out<A>, hx: {True{} == holds(A, x) : Bool}, hy: {True{} == holds(A, y) : Bool}) ->
  {True{} == holds(A, Bool.pick(Out<A>, b, x, y)) : Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

def bump_inv(+a: Nat, +b: Nat, +v: Nat, e: {True{} == Nat.is_eq(a, b) : Bool}) ->
  {True{} == Nat.is_eq(Nat.add(a, v), Nat.add(b, v)) : Bool}:
  %N.eq_sound(a, b, e) : {True{} == Nat.is_eq(Nat.add(a, v), Nat.add(_, v)) : Bool}
  N.eq_refl(Nat.add(a, v))

# A closed drive of a revert or a success gives it back.
def closed_revert(steps: List<&2, Step>) -> {True{} == holds(Unit, drive(~good, steps, Unit, False{}, Revert{})) : Bool}:
  match steps:
    case Nil{}:
      {==}
    case step <> _:
      match step:
        case Enter{_, _, _, _}:
          {==}
        case Answer{_, _, _}:
          {==}

def closed_ok(steps: List<&2, Step>, +t: Evm.State, h: {True{} == inv(t) : Bool}) ->
  {True{} == holds(Unit, drive(~good, steps, Unit, False{}, Ok{Unit{}, t})) : Bool}:
  match steps:
    case Nil{}:
      h
    case step <> _:
      match step:
        case Enter{_, _, _, _}:
          h
        case Answer{_, _, _}:
          h

# The end of pay, after the call gives x.
def resume_keep(+x: Nat, steps: List<&2, Step>, +t: Evm.State, h: {True{} == inv(t) : Bool}) ->
  {True{} == holds(Unit, drive(~good, steps, Unit, False{}, Bool.pick(Out<Unit>, Nat.is_eq(x, 1n), Ok{Unit{}, t}, Revert{}))) : Bool}:
  match x:
    case 0n:
      closed_revert(steps)
    case 1n+y:
      match y:
        case 0n:
          closed_ok(steps, t, h)
        case 1n+_:
          closed_revert(steps)

# pay's call answered, from a state that keeps the rule, when the
# callbacks of the answer keep it.
def answer_keep(+q: Evm.Call, +cbs: List<&2, Step>, +x: Nat, +rest: List<&2, Step>, +to: Nat, +v: Nat, +s: Evm.State,
  h: {True{} == inv(s) : Bool}, hc: {True{} == holds(Unit, drive(~good, cbs, Unit, True{}, Ok{Unit{}, s})) : Bool}) ->
  {True{} == holds(Unit, drive(~good, Answer{q, cbs, x} <> rest, Unit, False{},
    Calling{Evm.Call{to, "pay", [v]}, s, x => t => Bool.pick(Out<Unit>, Nat.is_eq(x, 1n), Ok{Unit{}, t}, Revert{})})) : Bool}:
  pick_keep(Unit, Evm.same.call(q, Evm.Call{to, "pay", [v]}),
    drive(~good, rest, Unit, False{}, Bool.pick(Out<Unit>, Nat.is_eq(x, 1n),
      Ok{Unit{}, after(Unit, s, drive(~good, cbs, Unit, True{}, Ok{Unit{}, s}))}, Revert{})), Revert{},
    resume_keep(x, rest, after(Unit, s, drive(~good, cbs, Unit, True{}, Ok{Unit{}, s})),
      after_keep(Unit, s, drive(~good, cbs, Unit, True{}, Ok{Unit{}, s}), h, hc)), {==})

# What an entry's proof needs about the first answer's callbacks.
def head_ok(inner: List<&2, Step>) -> Type:
  match inner:
    case Nil{}:
      Unit
    case step <> _:
      match step:
        case Enter{_, _, _, _}:
          Unit
        case Answer{_, cbs, _}:
          @t: Evm.State -> {True{} == inv(t) : Bool} -> {True{} == holds(Unit, drive(~good, cbs, Unit, True{}, Ok{Unit{}, t})) : Bool}

# Each entry keeps the rule when a callee calls it back.
def entry_keep(+entry: Nat, +args: List<&2, Nat>, +sender: Nat, +s: Evm.State, +h: {True{} == inv(s) : Bool},
  +inner: List<&2, Step>, ih: head_ok(inner)) ->
  {True{} == holds(Unit, drive(~good, inner, Unit, False{}, good(entry, args, Unit, u => w => Ok{u, w}, with.caller(sender, s)))) : Bool}:
  match entry:
    case 0n:
      match args:
        case Nil{}:
          closed_revert(inner)
        case +v <> _:
          match s:
            case Evm.State{+storage, _, +limit, +logs, +world}:
              closed_ok(inner, Evm.State{Evm.Slot{Evm.Plain{1n}, Nat.add(Evm.lookup(storage, Evm.Plain{1n}), v)} <> Evm.Slot{Evm.Plain{0n}, Nat.add(Evm.lookup(storage, Evm.Plain{0n}), v)} <> storage, sender, limit, logs, world}, bump_inv(Evm.lookup(storage, Evm.Plain{0n}), Evm.lookup(storage, Evm.Plain{1n}), v, h))
    case 1n+j:
      match j:
        case 0n:
          match args:
            case Nil{}:
              closed_revert(inner)
            case +to <> more:
              match more:
                case Nil{}:
                  closed_revert(inner)
                case +v <> _:
                  match s:
                    case Evm.State{+storage, _, +limit, +logs, +world}:
                      match inner:
                        case Nil{}:
                          {==}
                        case step <> +rest:
                          match step:
                            case Enter{_, _, _, _}:
                              {==}
                            case Answer{+q, +cbs, +x}:
                              +t : Evm.State = Evm.State{Evm.Slot{Evm.Plain{1n}, Nat.add(Evm.lookup(storage, Evm.Plain{1n}), v)} <> Evm.Slot{Evm.Plain{0n}, Nat.add(Evm.lookup(storage, Evm.Plain{0n}), v)} <> storage, sender, limit, logs, world}
                              answer_keep(q, cbs, x, rest, to, v, t, bump_inv(Evm.lookup(storage, Evm.Plain{0n}), Evm.lookup(storage, Evm.Plain{1n}), v, h), ih(t, bump_inv(Evm.lookup(storage, Evm.Plain{0n}), Evm.lookup(storage, Evm.Plain{1n}), v, h)))
        case 1n+_:
          closed_revert(inner)

# Any list of callbacks keeps the rule.
def callbacks_keep(steps: List<&2, Step>, +s: Evm.State, +h: {True{} == inv(s) : Bool}) ->
  {True{} == holds(Unit, drive(~good, steps, Unit, True{}, Ok{Unit{}, s})) : Bool}:
  match steps:
    case Nil{}:
      h
    case step <> rest:
      match step:
        case Answer{_, _, _}:
          h
        case Enter{+sender, +entry, +args, +inner}:
          match inner:
            case Nil{}:
              callbacks_keep(rest, back(Unit, s, drive(~good, Nil{}, Unit, False{}, good(entry, args, Unit, u => w => Ok{u, w}, with.caller(sender, s)))),
                back_keep(Unit, s, drive(~good, Nil{}, Unit, False{}, good(entry, args, Unit, u => w => Ok{u, w}, with.caller(sender, s))), h, entry_keep(entry, args, sender, s, h, Nil{}, Unit{})))
            case first <> +more:
              match first:
                case Enter{+a, +b, +c, +d}:
                  callbacks_keep(rest, back(Unit, s, drive(~good, Enter{a, b, c, d} <> more, Unit, False{}, good(entry, args, Unit, u => w => Ok{u, w}, with.caller(sender, s)))),
                back_keep(Unit, s, drive(~good, Enter{a, b, c, d} <> more, Unit, False{}, good(entry, args, Unit, u => w => Ok{u, w}, with.caller(sender, s))), h, entry_keep(entry, args, sender, s, h, Enter{a, b, c, d} <> more, Unit{})))
                case Answer{+q, +cbs, +x}:
                  callbacks_keep(rest, back(Unit, s, drive(~good, Answer{q, cbs, x} <> more, Unit, False{}, good(entry, args, Unit, u => w => Ok{u, w}, with.caller(sender, s)))),
                back_keep(Unit, s, drive(~good, Answer{q, cbs, x} <> more, Unit, False{}, good(entry, args, Unit, u => w => Ok{u, w}, with.caller(sender, s))), h, entry_keep(entry, args, sender, s, h, Answer{q, cbs, x} <> more, t => ht => callbacks_keep(cbs, t, ht))))

# The theorem: from a state that keeps the rule, pay keeps it, for every
# list of answers, so for every callee and every callback it makes.
def pay_keeps(steps: List<&2, Step>, +to: Nat, +v: Nat, +s: Evm.State, +h: {True{} == inv(s) : Bool}) ->
  {True{} == holds(Unit, exec(~good, Unit, pay(to, v), steps, s)) : Bool}:
  match steps:
    case Nil{}:
      {==}
    case step <> +rest:
      match step:
        case Enter{_, _, _, _}:
          {==}
        case Answer{+q, +cbs, +x}:
          match s:
            case Evm.State{+storage, +who, +limit, +logs, +world}:
              +t : Evm.State = Evm.State{Evm.Slot{Evm.Plain{1n}, Nat.add(Evm.lookup(storage, Evm.Plain{1n}), v)} <> Evm.Slot{Evm.Plain{0n}, Nat.add(Evm.lookup(storage, Evm.Plain{0n}), v)} <> storage, who, limit, logs, world}
              +ht : {True{} == inv(t) : Bool} = bump_inv(Evm.lookup(storage, Evm.Plain{0n}), Evm.lookup(storage, Evm.Plain{1n}), v, h)
              answer_keep(q, cbs, x, rest, to, v, t, ht, callbacks_keep(cbs, t, ht))

# In the bad order, the callback above leaves the slots unequal.
def broken_rule(who: Nat, limit: Nat, logs: List<&2, Evm.Log>, world: Evm.World) ->
  {False{} == inv(Evm.State{[Evm.Slot{Evm.Plain{1n}, 5n}, Evm.Slot{Evm.Plain{1n}, 9n}, Evm.Slot{Evm.Plain{0n}, 14n}, Evm.Slot{Evm.Plain{0n}, 5n}],
    who, limit, logs, world}) : Bool}:
  {==}
