import Base
import ../../src/Evm.bend as Evm
import ./program.bend as Counter

# Each law gives every outcome from any state: any storage, caller, word
# limit and earlier logs. The counter is plain slot 0.

def count(storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{0n})

law get:
  for +storage: List<&2, Evm.Slot>
  for who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  {Evm.run(Nat, Counter.get(), Evm.State{storage, who, limit, logs})
    == Evm.Ok{count(storage), Evm.State{storage, who, limit, logs}} : Evm.Outcome<Nat>}

law increment:
  for +storage: List<&2, Evm.Slot>
  for who: Nat
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  {Evm.run(Unit, Counter.increment(), Evm.State{storage, who, limit, logs})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(count(storage), 1n), limit),
      Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{0n}, Nat.add(count(storage), 1n)} <> storage, who, limit, logs}},
      Evm.Revert{}) : Evm.Outcome<Unit>}

law decrement:
  for +storage: List<&2, Evm.Slot>
  for who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  {Evm.run(Unit, Counter.decrement(), Evm.State{storage, who, limit, logs})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(count(storage), 1n),
      Evm.Revert{},
      Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{0n}, Nat.sub(count(storage), 1n)} <> storage, who, limit, logs}})
    : Evm.Outcome<Unit>}

# Only the owner can set.
law set:
  for storage: List<&2, Evm.Slot>
  for +who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for value: Nat
  {Evm.run(Unit, Counter.set(value), Evm.State{storage, who, limit, logs})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(who, Counter.owner()),
      Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{0n}, value} <> storage, who, limit, logs}},
      Evm.Revert{}) : Evm.Outcome<Unit>}
