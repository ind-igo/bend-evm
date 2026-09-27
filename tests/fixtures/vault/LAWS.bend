import Base
import ../../../src/Evm.bend as Evm
import ../../../src/calls.bend as Calls
import ../../../src/sum.bend as Sum
import ./program.bend as Program
import ./CERT.bend as Cert

def shares(+storage: List<&2, Evm.Slot>, +who: Nat) -> Nat:
  Evm.lookup(storage, Evm.Mapped{Evm.Plain{0n}, who})

def total(+storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{1n})

def token(+storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{2n})

# The state with who's shares and the total set, before the call.
def moved(+storage: List<&2, Evm.Slot>, +who: Nat, limit: Nat, logs: List<&2, Evm.Log>, world: Evm.World,
  held: Nat, sum: Nat) -> Evm.State:
  Evm.State{Evm.Slot{Evm.Plain{1n}, sum} <> Evm.Slot{Evm.Mapped{Evm.Plain{0n}, who}, held} <> storage, who, limit, logs, world}

# With no callbacks, withdraw takes the shares, then calls transfer, and
# ends when the token returns 1. The answer must be for that call.
law withdraw:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +q: Evm.Call
  for +amount: Nat
  for e1: {False{} == Nat.is_lt(shares(storage, who), amount) : Bool}
  for e2: {False{} == Nat.is_lt(total(storage), amount) : Bool}
  {Calls.run(Cert.entry.table(), Unit, Program.withdraw(amount), [Calls.Answer{q, [], 1n}], Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Evm.same.call(q, Evm.Call{token(storage), "transfer", [who, amount]}),
      Evm.Ok{Unit{}, moved(storage, who, limit, logs, world, Nat.sub(shares(storage, who), amount), Nat.sub(total(storage), amount))},
      Evm.Revert{}) : Evm.Outcome<Unit>}

# With any callbacks, deposit gives the shares first, so the callbacks run
# on the state with the new shares, and the deposit ends in the state that
# they leave.
law deposit:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +q: Evm.Call
  for +cbs: List<&2, Calls.Step>
  for +amount: Nat
  for e1: {True{} == Nat.is_lt(Nat.add(shares(storage, who), amount), limit) : Bool}
  for e2: {True{} == Nat.is_lt(Nat.add(total(storage), amount), limit) : Bool}
  {Calls.run(Cert.entry.table(), Unit, Program.deposit(amount), [Calls.Answer{q, cbs, 1n}], Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Evm.same.call(q, Evm.Call{token(storage), "transferFrom", [who, Evm.self.of(world), amount]}),
      Evm.Ok{Unit{}, Calls.after(Unit,
        moved(storage, who, limit, logs, world, Nat.add(shares(storage, who), amount), Nat.add(total(storage), amount)),
        Calls.drive(Calls.Model{}, Cert.entry.table(), cbs, Unit, True{}, Evm.Ok{Unit{},
          moved(storage, who, limit, logs, world, Nat.add(shares(storage, who), amount), Nat.add(total(storage), amount))}))},
      Evm.Revert{}) : Evm.Outcome<Unit>}

# A callback from another sender runs inside the call, and after it the
# caller is this call's caller again. Here the callback reads totalShares,
# the entry at index 2 of the certificate's table.
law touch:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +q: Evm.Call
  for +other: Nat
  for +x: Nat
  for +y: Nat
  {Calls.run(Cert.entry.table(), Unit, Program.touch(x), [Calls.Answer{q, [Calls.Enter{other, 2n, [], []}], y}],
      Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Evm.same.call(q, Evm.Call{token(storage), "ping", [x]}),
      Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{3n}, who} <> storage, who, limit, logs, world}},
      Evm.Revert{}) : Evm.Outcome<Unit>}

# The total is the sum of the shares of the listed accounts.
def balanced(s: Evm.State, +accounts: List<&2, Nat>) -> Bool:
  match s:
    case Evm.State{+storage, _, _, _, _}:
      Nat.is_eq(total(storage), Sum.holdings(storage, 0n, accounts))

# Each sender in the steps, at any depth, is in the list once.
def listed(steps: List<&2, Calls.Step>, +accounts: List<&2, Nat>) -> Bool:
  match steps:
    case Nil{}:
      True{}
    case step <> rest:
      match step:
        case Calls.Enter{+sender, _, _, inner}:
          Bool.and(Nat.is_eq(1n, Sum.count(sender, accounts)), Bool.and(listed(inner, accounts), listed(rest, accounts)))
        case Calls.Answer{_, cbs, _}:
          Bool.and(listed(cbs, accounts), listed(rest, accounts))

# Any callbacks keep the total equal to the sum of the shares: any entries,
# from any listed senders, with any answers, and with callbacks inside those
# answers at any depth. Transactions are callbacks from outside, so this
# holds for any list of them too. The callbacks law in src/LAWS.bend gives
# the same for the compiled entries.
law shares_sum:
  for +steps: List<&2, Calls.Step>
  for +s: Evm.State
  for +accounts: List<&2, Nat>
  for +h: {True{} == balanced(s, accounts) : Bool}
  for +l: {True{} == listed(steps, accounts) : Bool}
  {True{} == balanced(Calls.after(Unit, s, Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, True{}, Evm.Ok{Unit{}, s})),
    accounts) : Bool}
