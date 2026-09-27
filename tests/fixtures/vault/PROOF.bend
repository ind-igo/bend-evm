import Base
import ../../../src/Evm.bend as Evm
import ../../../src/calls.bend as Calls
import ../../../src/nat.bend as N
import ../../../src/sum.bend as Sum
import ./program.bend as Program
import ./CERT.bend as Cert
import ./LAWS.bend as Laws

# The checks before the call are picks that the run cannot pass until the
# hypotheses decide them.

def paying(+storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  +amount: Nat) -> Evm.Outcome<Unit>:
  Evm.Calling{Evm.Call{Laws.token(storage), "transfer", [who, amount]},
    Laws.moved(storage, who, limit, logs, world, Nat.sub(Laws.shares(storage, who), amount), Nat.sub(Laws.total(storage), amount)),
    x => t => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n), Evm.Ok{Unit{}, t}, Evm.Revert{})}

def taking(+storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  +amount: Nat) -> Evm.Outcome<Unit>:
  Evm.Calling{Evm.Call{Laws.token(storage), "transferFrom", [who, Evm.self.of(world), amount]},
    Laws.moved(storage, who, limit, logs, world, Nat.add(Laws.shares(storage, who), amount), Nat.add(Laws.total(storage), amount)),
    x => t => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n), Evm.Ok{Unit{}, t}, Evm.Revert{})}

def Laws.withdraw(storage, who, limit, logs, world, q, cbs, amount, e1, e2):
  -steps = {[Calls.Answer{q, cbs, 1n}] : List<&2, Calls.Step>}
  -after = {Laws.moved(storage, who, limit, logs, world, Nat.sub(Laws.shares(storage, who), amount), Nat.sub(Laws.total(storage), amount)) : Evm.State}
  -rhs = {Bool.pick(Evm.Outcome<Unit>, Evm.same.call(q, Evm.Call{Laws.token(storage), "transfer", [who, amount]}),
      Evm.Ok{Unit{}, Calls.after(Unit, after, Calls.drive(Calls.Model{}, Cert.entry.table(), cbs, Unit, True{}, Evm.Ok{Unit{}, after}))},
      Evm.Revert{}) : Evm.Outcome<Unit>}
  %e1 : {Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, False{}, Bool.pick(Evm.Outcome<Unit>, _, Evm.Revert{},
    Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Laws.total(storage), amount), Evm.Revert{}, paying(storage, who, limit, logs, world, amount))))
    == rhs : Evm.Outcome<Unit>}
  %e2 : {Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, False{},
    Bool.pick(Evm.Outcome<Unit>, _, Evm.Revert{}, paying(storage, who, limit, logs, world, amount))) == rhs : Evm.Outcome<Unit>}
  {==}

def Laws.deposit(storage, who, limit, logs, world, q, cbs, amount, e1, e2):
  -steps = {[Calls.Answer{q, cbs, 1n}] : List<&2, Calls.Step>}
  -after = {Laws.moved(storage, who, limit, logs, world, Nat.add(Laws.shares(storage, who), amount), Nat.add(Laws.total(storage), amount)) : Evm.State}
  -rhs = {Bool.pick(Evm.Outcome<Unit>, Evm.same.call(q, Evm.Call{Laws.token(storage), "transferFrom", [who, Evm.self.of(world), amount]}),
      Evm.Ok{Unit{}, Calls.after(Unit, after, Calls.drive(Calls.Model{}, Cert.entry.table(), cbs, Unit, True{}, Evm.Ok{Unit{}, after}))},
      Evm.Revert{}) : Evm.Outcome<Unit>}
  %e1 : {Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, False{}, Bool.pick(Evm.Outcome<Unit>, _,
    Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.total(storage), amount), limit), taking(storage, who, limit, logs, world, amount), Evm.Revert{}),
    Evm.Revert{})) == rhs : Evm.Outcome<Unit>}
  %e2 : {Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, False{},
    Bool.pick(Evm.Outcome<Unit>, _, taking(storage, who, limit, logs, world, amount), Evm.Revert{})) == rhs : Evm.Outcome<Unit>}
  {==}

def Laws.touch(storage, who, limit, logs, world, q, other, x, y):
  {==}

# ---- shares_sum: an invariant across every callback ----
#
# holds says that an outcome keeps the invariant. The proof goes by
# induction on the callbacks. Each entry of the table keeps the invariant
# when the callbacks in the answers to its call keep it (head_ok), and the
# induction gives that for the callbacks inside each answer.

def closed(steps: List<&2, Calls.Step>, o: Evm.Outcome<Unit>) -> Evm.Outcome<Unit>:
  Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, False{}, o)

def opened(steps: List<&2, Calls.Step>, s: Evm.State) -> Evm.Outcome<Unit>:
  Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, True{}, Evm.Ok{Unit{}, s})

# The run of a callback: entry i with the arguments, from sender.
def entered(+i: Nat, +args: List<&2, Nat>, +sender: Nat, +s: Evm.State, inner: List<&2, Calls.Step>) -> Evm.Outcome<Unit>:
  closed(inner, Calls.callback(Calls.Model{}, Cert.entry.table(), i, args, Unit, u => w => Evm.Ok{u, w}, Calls.with.caller(sender, s)))

def holds(o: Evm.Outcome<Unit>, +accounts: List<&2, Nat>) -> Bool:
  match o:
    case Evm.Ok{_, t}:
      Laws.balanced(t, accounts)
    case Evm.Revert{}:
      True{}
    case Evm.Raise{_}:
      True{}
    case Evm.Calling{_, _, _}:
      True{}

def pick_keep(+b: Bool, -x: Evm.Outcome<Unit>, -y: Evm.Outcome<Unit>, -accounts: List<&2, Nat>,
  hx: {True{} == b : Bool} -> {True{} == holds(x, accounts) : Bool},
  hy: {False{} == b : Bool} -> {True{} == holds(y, accounts) : Bool}) ->
  {True{} == holds(Bool.pick(Evm.Outcome<Unit>, b, x, y), accounts) : Bool}:
  match b:
    case True{}:
      hx({==})
    case False{}:
      hy({==})

def closed_pick(-steps: List<&2, Calls.Step>, +b: Bool, -x: Evm.Outcome<Unit>, -y: Evm.Outcome<Unit>, -accounts: List<&2, Nat>,
  hx: {True{} == b : Bool} -> {True{} == holds(closed(steps, x), accounts) : Bool},
  hy: {False{} == b : Bool} -> {True{} == holds(closed(steps, y), accounts) : Bool}) ->
  {True{} == holds(closed(steps, Bool.pick(Evm.Outcome<Unit>, b, x, y)), accounts) : Bool}:
  match b:
    case True{}:
      hx({==})
    case False{}:
      hy({==})

def closed_revert(steps: List<&2, Calls.Step>, -accounts: List<&2, Nat>) ->
  {True{} == holds(closed(steps, Evm.Revert{}), accounts) : Bool}:
  match steps:
    case Nil{}:
      {==}
    case step <> _:
      match step:
        case Calls.Enter{_, _, _, _}:
          {==}
        case Calls.Answer{_, _, _}:
          {==}

def closed_ok(steps: List<&2, Calls.Step>, -t: Evm.State, -accounts: List<&2, Nat>, h: {True{} == Laws.balanced(t, accounts) : Bool}) ->
  {True{} == holds(closed(steps, Evm.Ok{Unit{}, t}), accounts) : Bool}:
  match steps:
    case Nil{}:
      h
    case step <> _:
      match step:
        case Calls.Enter{_, _, _, _}:
          h
        case Calls.Answer{_, _, _}:
          h

def after_keep(-s: Evm.State, o: Evm.Outcome<Unit>, -accounts: List<&2, Nat>,
  hs: {True{} == Laws.balanced(s, accounts) : Bool}, ho: {True{} == holds(o, accounts) : Bool}) ->
  {True{} == Laws.balanced(Calls.after(Unit, s, o), accounts) : Bool}:
  match o:
    case Evm.Ok{_, _}:
      ho
    case Evm.Revert{}:
      hs
    case Evm.Raise{_}:
      hs
    case Evm.Calling{_, _, _}:
      hs

def back_keep(-s: Evm.State, o: Evm.Outcome<Unit>, -accounts: List<&2, Nat>,
  hs: {True{} == Laws.balanced(s, accounts) : Bool}, ho: {True{} == holds(o, accounts) : Bool}) ->
  {True{} == Laws.balanced(Calls.back(Unit, s, o), accounts) : Bool}:
  match o:
    case Evm.Ok{_, t}:
      match t:
        case Evm.State{_, _, _, _, _}:
          ho
    case Evm.Revert{}:
      hs
    case Evm.Raise{_}:
      hs
    case Evm.Calling{_, _, _}:
      hs

# What an entry needs about the callbacks in the first answer.
def head_ok(inner: List<&2, Calls.Step>, +accounts: List<&2, Nat>) -> Type:
  match inner:
    case Nil{}:
      Unit
    case step <> _:
      match step:
        case Calls.Enter{_, _, _, _}:
          Unit
        case Calls.Answer{_, cbs, _}:
          @t: Evm.State -> {True{} == Laws.balanced(t, accounts) : Bool} -> {True{} == holds(opened(cbs, t), accounts) : Bool}

# A call from a state that keeps the invariant, when the rest of the entry
# keeps it from any state that keeps it.
def calling(inner: List<&2, Calls.Step>, +c: Evm.Call, +t: Evm.State, -r: Nat -> Evm.State -> Evm.Outcome<Unit>, -accounts: List<&2, Nat>,
  +ht: {True{} == Laws.balanced(t, accounts) : Bool},
  hr: @x: Nat -> @rest: List<&2, Calls.Step> -> @u: Evm.State -> {True{} == Laws.balanced(u, accounts) : Bool} ->
    {True{} == holds(closed(rest, r(x, u)), accounts) : Bool},
  ih: head_ok(inner, accounts)) ->
  {True{} == holds(closed(inner, Evm.Calling{c, t, r}), accounts) : Bool}:
  match inner:
    case Nil{}:
      {==}
    case step <> +rest:
      match step:
        case Calls.Enter{_, _, _, _}:
          {==}
        case Calls.Answer{+q, +cbs, +x}:
          pick_keep(Evm.same.call(q, c), closed(rest, r(x, Calls.after(Unit, t, opened(cbs, t)))), Evm.Revert{}, accounts,
            _ => hr(x, rest, Calls.after(Unit, t, opened(cbs, t)), after_keep(t, opened(cbs, t), accounts, ht, ih(t, ht))),
            _ => {==})

# The end of deposit and withdraw: the call must give 1.
def settled(+x: Nat, +rest: List<&2, Calls.Step>, -u: Evm.State, -accounts: List<&2, Nat>, +hu: {True{} == Laws.balanced(u, accounts) : Bool}) ->
  {True{} == holds(closed(rest, Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n), Evm.Ok{Unit{}, u}, Evm.Revert{})), accounts) : Bool}:
  closed_pick(rest, Nat.is_eq(x, 1n), Evm.Ok{Unit{}, u}, Evm.Revert{}, accounts,
    _ => closed_ok(rest, u, accounts, hu),
    _ => closed_revert(rest, accounts))

def deposited(+storage: List<&2, Evm.Slot>, +sender: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World, +amount: Nat,
  +accounts: List<&2, Nat>, +h: {True{} == Nat.is_eq(Laws.total(storage), Sum.holdings(storage, 0n, accounts)) : Bool},
  +c: {1n == Sum.count(sender, accounts) : Nat}) ->
  {True{} == Laws.balanced(Laws.moved(storage, sender, limit, logs, world, Nat.add(Laws.shares(storage, sender), amount),
    Nat.add(Laws.total(storage), amount)), accounts) : Bool}:
  %Sum.skip_plain(Sum.credited(storage, 0n, sender, amount), 0n, 1n, Nat.add(Laws.total(storage), amount), accounts) :
    {True{} == Nat.is_eq(Nat.add(Laws.total(storage), amount), _) : Bool}
  %Sum.credit_once(storage, 0n, sender, amount, accounts, c) :
    {True{} == Nat.is_eq(Nat.add(Laws.total(storage), amount), _) : Bool}
  %N.eq_sound(Laws.total(storage), Sum.holdings(storage, 0n, accounts), h) :
    {True{} == Nat.is_eq(Nat.add(Laws.total(storage), amount), Nat.add(_, amount)) : Bool}
  N.eq_refl(Nat.add(Laws.total(storage), amount))

def withdrawn(+storage: List<&2, Evm.Slot>, +sender: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World, +amount: Nat,
  +accounts: List<&2, Nat>, +h: {True{} == Nat.is_eq(Laws.total(storage), Sum.holdings(storage, 0n, accounts)) : Bool},
  +e: {False{} == Nat.is_lt(Laws.shares(storage, sender), amount) : Bool}, +c: {1n == Sum.count(sender, accounts) : Nat}) ->
  {True{} == Laws.balanced(Laws.moved(storage, sender, limit, logs, world, Nat.sub(Laws.shares(storage, sender), amount),
    Nat.sub(Laws.total(storage), amount)), accounts) : Bool}:
  -d = {Sum.holdings(Sum.debited(storage, 0n, sender, amount), 0n, accounts) : Nat}
  %Sum.skip_plain(Sum.debited(storage, 0n, sender, amount), 0n, 1n, Nat.sub(Laws.total(storage), amount), accounts) :
    {True{} == Nat.is_eq(Nat.sub(Laws.total(storage), amount), _) : Bool}
  %Equal.sym(Nat, Laws.total(storage), Sum.holdings(storage, 0n, accounts),
    N.eq_sound(Laws.total(storage), Sum.holdings(storage, 0n, accounts), h)) :
    {True{} == Nat.is_eq(Nat.sub(_, amount), d) : Bool}
  %Sum.debit_once(storage, 0n, sender, amount, accounts, e, c) : {True{} == Nat.is_eq(Nat.sub(_, amount), d) : Bool}
  %N.add_comm(amount, Sum.holdings(Sum.debited(storage, 0n, sender, amount), 0n, accounts)) :
    {True{} == Nat.is_eq(Nat.sub(_, amount), d) : Bool}
  %N.sub_add_cancel(Sum.holdings(Sum.debited(storage, 0n, sender, amount), 0n, accounts), amount) :
    {True{} == Nat.is_eq(_, d) : Bool}
  N.eq_refl(Sum.holdings(Sum.debited(storage, 0n, sender, amount), 0n, accounts))

def slot3(+storage: List<&2, Evm.Slot>, +v: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.total(storage), Sum.holdings(storage, 0n, accounts)) : Bool}) ->
  {True{} == Nat.is_eq(Laws.total(storage), Sum.holdings(Evm.Slot{Evm.Plain{3n}, v} <> storage, 0n, accounts)) : Bool}:
  %Sum.skip_plain(storage, 0n, 3n, v, accounts) : {True{} == Nat.is_eq(Laws.total(storage), _) : Bool}
  h

# touch writes slot 3, which is not a share.
def touched(rest: List<&2, Calls.Step>, +u: Evm.State, +accounts: List<&2, Nat>, +hu: {True{} == Laws.balanced(u, accounts) : Bool}) ->
  {True{} == holds(closed(rest, Evm.Ok{Unit{}, Evm.write.go(Evm.Plain{3n}, Evm.caller.of(u), u)}), accounts) : Bool}:
  match u:
    case Evm.State{+storage, +caller, +limit, +logs, +world}:
      closed_ok(rest, Evm.State{Evm.Slot{Evm.Plain{3n}, caller} <> storage, caller, limit, logs, world}, accounts,
        slot3(storage, caller, accounts, hu))

# Each entry of the table, in the table's order.
def entry_keep(+i: Nat, +args: List<&2, Nat>, +sender: Nat, +s: Evm.State, +accounts: List<&2, Nat>,
  +h: {True{} == Laws.balanced(s, accounts) : Bool}, +c: {1n == Sum.count(sender, accounts) : Nat},
  +inner: List<&2, Calls.Step>, ih: head_ok(inner, accounts)) ->
  {True{} == holds(entered(i, args, sender, s, inner), accounts) : Bool}:
  match i:
    case 0n:
      match s:
        case Evm.State{+storage, _, +limit, +logs, +world}:
          closed_ok(inner, Evm.State{storage, sender, limit, logs, world}, accounts, h)
    case 1n:
      match args:
        case Nil{}:
          closed_revert(inner, accounts)
        case _ <> _:
          match s:
            case Evm.State{+storage, _, +limit, +logs, +world}:
              closed_ok(inner, Evm.State{storage, sender, limit, logs, world}, accounts, h)
    case 2n:
      match s:
        case Evm.State{+storage, _, +limit, +logs, +world}:
          closed_ok(inner, Evm.State{storage, sender, limit, logs, world}, accounts, h)
    case 3n:
      match args:
        case Nil{}:
          closed_revert(inner, accounts)
        case +amount <> _:
          match s:
            case Evm.State{+storage, _, +limit, +logs, +world}:
              closed_pick(inner, Nat.is_lt(Nat.add(Laws.shares(storage, sender), amount), limit),
                Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.total(storage), amount), limit),
                  taking(storage, sender, limit, logs, world, amount), Evm.Revert{}),
                Evm.Revert{}, accounts,
                _ => closed_pick(inner, Nat.is_lt(Nat.add(Laws.total(storage), amount), limit),
                  taking(storage, sender, limit, logs, world, amount), Evm.Revert{}, accounts,
                  _ => calling(inner, Evm.Call{Laws.token(storage), "transferFrom", [sender, Evm.self.of(world), amount]},
                    Laws.moved(storage, sender, limit, logs, world, Nat.add(Laws.shares(storage, sender), amount), Nat.add(Laws.total(storage), amount)),
                    x => t => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n), Evm.Ok{Unit{}, t}, Evm.Revert{}), accounts,
                    deposited(storage, sender, limit, logs, world, amount, accounts, h, c),
                    x => rest => u => hu => settled(x, rest, u, accounts, hu), ih),
                  _ => closed_revert(inner, accounts)),
                _ => closed_revert(inner, accounts))
    case 4n:
      match args:
        case Nil{}:
          closed_revert(inner, accounts)
        case +amount <> _:
          match s:
            case Evm.State{+storage, _, +limit, +logs, +world}:
              closed_pick(inner, Nat.is_lt(Laws.shares(storage, sender), amount), Evm.Revert{},
                Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Laws.total(storage), amount), Evm.Revert{},
                  paying(storage, sender, limit, logs, world, amount)), accounts,
                _ => closed_revert(inner, accounts),
                e => closed_pick(inner, Nat.is_lt(Laws.total(storage), amount), Evm.Revert{},
                  paying(storage, sender, limit, logs, world, amount), accounts,
                  _ => closed_revert(inner, accounts),
                  _ => calling(inner, Evm.Call{Laws.token(storage), "transfer", [sender, amount]},
                    Laws.moved(storage, sender, limit, logs, world, Nat.sub(Laws.shares(storage, sender), amount), Nat.sub(Laws.total(storage), amount)),
                    x => t => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n), Evm.Ok{Unit{}, t}, Evm.Revert{}), accounts,
                    withdrawn(storage, sender, limit, logs, world, amount, accounts, h, e, c),
                    x => rest => u => hu => settled(x, rest, u, accounts, hu), ih)))
    case 5n:
      match args:
        case Nil{}:
          closed_revert(inner, accounts)
        case +x <> _:
          match s:
            case Evm.State{+storage, _, +limit, +logs, +world}:
              calling(inner, Evm.Call{Laws.token(storage), "ping", [x]}, Evm.State{storage, sender, limit, logs, world},
                y => u => Evm.Ok{Unit{}, u}, accounts, h,
                y => rest => u => hu => closed_ok(rest, u, accounts, hu), ih)
    case 6n:
      match args:
        case Nil{}:
          closed_revert(inner, accounts)
        case +x <> _:
          match s:
            case Evm.State{+storage, _, +limit, +logs, +world}:
              calling(inner, Evm.Call{Laws.token(storage), "ping", [x]}, Evm.State{storage, sender, limit, logs, world},
                y => u => Evm.Ok{Unit{}, Evm.write.go(Evm.Plain{3n}, Evm.caller.of(u), u)}, accounts, h,
                y => rest => u => hu => touched(rest, u, accounts, hu), ih)
    case 7n+_:
      closed_revert(inner, accounts)

# One callback, then the rest.
def enter(+sender: Nat, +i: Nat, +args: List<&2, Nat>, +inner: List<&2, Calls.Step>, +rest: List<&2, Calls.Step>, +s: Evm.State,
  +accounts: List<&2, Nat>, +h: {True{} == Laws.balanced(s, accounts) : Bool},
  +l: {True{} == Laws.listed(Calls.Enter{sender, i, args, inner} <> rest, accounts) : Bool}, ih: head_ok(inner, accounts),
  k: @t: Evm.State -> {True{} == Laws.balanced(t, accounts) : Bool} -> {True{} == Laws.listed(rest, accounts) : Bool} ->
    {True{} == holds(opened(rest, t), accounts) : Bool}) ->
  {True{} == holds(opened(Calls.Enter{sender, i, args, inner} <> rest, s), accounts) : Bool}:
  k(Calls.back(Unit, s, entered(i, args, sender, s, inner)),
    back_keep(s, entered(i, args, sender, s, inner), accounts, h,
      entry_keep(i, args, sender, s, accounts, h,
        N.eq_sound(1n, Sum.count(sender, accounts),
          N.and_left(Nat.is_eq(1n, Sum.count(sender, accounts)), Bool.and(Laws.listed(inner, accounts), Laws.listed(rest, accounts)), l)),
        inner, ih)),
    N.and_right(Laws.listed(inner, accounts), Laws.listed(rest, accounts),
      N.and_right(Nat.is_eq(1n, Sum.count(sender, accounts)), Bool.and(Laws.listed(inner, accounts), Laws.listed(rest, accounts)), l)))

# Any list of callbacks keeps the invariant.
def callbacks_keep(steps: List<&2, Calls.Step>, +s: Evm.State, +accounts: List<&2, Nat>,
  +h: {True{} == Laws.balanced(s, accounts) : Bool}, +l: {True{} == Laws.listed(steps, accounts) : Bool}) ->
  {True{} == holds(opened(steps, s), accounts) : Bool}:
  match steps:
    case Nil{}:
      h
    case step <> +rest:
      match step:
        case Calls.Answer{_, _, _}:
          h
        case Calls.Enter{+sender, +i, +args, +inner}:
          match inner:
            case Nil{}:
              enter(sender, i, args, Nil{}, rest, s, accounts, h, l, Unit{},
                t => ht => lr => callbacks_keep(rest, t, accounts, ht, lr))
            case +first <> +more:
              match first:
                case Calls.Enter{+a, +b, +d, +e}:
                  enter(sender, i, args, Calls.Enter{a, b, d, e} <> more, rest, s, accounts, h, l, Unit{},
                    t => ht => lr => callbacks_keep(rest, t, accounts, ht, lr))
                case Calls.Answer{+q, +cbs, +x}:
                  enter(sender, i, args, Calls.Answer{q, cbs, x} <> more, rest, s, accounts, h, l,
                    t => ht => callbacks_keep(cbs, t, accounts, ht,
                      N.and_left(Laws.listed(cbs, accounts), Laws.listed(more, accounts),
                        N.and_left(Laws.listed(Calls.Answer{q, cbs, x} <> more, accounts), Laws.listed(rest, accounts),
                          N.and_right(Nat.is_eq(1n, Sum.count(sender, accounts)),
                            Bool.and(Laws.listed(Calls.Answer{q, cbs, x} <> more, accounts), Laws.listed(rest, accounts)), l)))),
                    t => ht => lr => callbacks_keep(rest, t, accounts, ht, lr))

def Laws.shares_sum(steps, s, accounts, h, l):
  after_keep(s, opened(steps, s), accounts, h, callbacks_keep(steps, s, accounts, h, l))
