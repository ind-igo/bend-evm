import Base
import ../../../src/Evm.bend as Evm
import ../../../src/calls.bend as Calls
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
  {Calls.run(Cert.entries(), Unit, Program.withdraw(amount), [Calls.Answer{q, [], 1n}], Evm.State{storage, who, limit, logs, world})
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
  {Calls.run(Cert.entries(), Unit, Program.deposit(amount), [Calls.Answer{q, cbs, 1n}], Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Evm.same.call(q, Evm.Call{token(storage), "transferFrom", [who, Evm.self.of(world), amount]}),
      Evm.Ok{Unit{}, Calls.after(Unit,
        moved(storage, who, limit, logs, world, Nat.add(shares(storage, who), amount), Nat.add(total(storage), amount)),
        Calls.drive(Calls.Model{}, Cert.entries(), cbs, Unit, True{}, Evm.Ok{Unit{},
          moved(storage, who, limit, logs, world, Nat.add(shares(storage, who), amount), Nat.add(total(storage), amount))}))},
      Evm.Revert{}) : Evm.Outcome<Unit>}
