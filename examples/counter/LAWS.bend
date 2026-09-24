import Base
import ../../src/Evm.bend as Evm
import ./program.bend as Counter

# The owner stores any value; the storage and word limit stay symbolic.
law set_by_owner:
  for storage: List<&2, Evm.Slot>
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for +value: Nat
  {Counter.set(value, Evm.State{storage, Counter.owner(), limit, logs})
    == Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{0n}, value} <> storage, Counter.owner(), limit, logs}} : Evm.Outcome<Unit>}

law set_by_other:
  for storage: List<&2, Evm.Slot>
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for value: Nat
  {Counter.set(value, Evm.State{storage, 8n, limit, logs}) == Evm.Revert{} : Evm.Outcome<Unit>}

law get_after_set:
  for storage: List<&2, Evm.Slot>
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for +value: Nat
  {Counter.get(Evm.State{Evm.Slot{Evm.Plain{0n}, value} <> storage, 7n, limit, logs})
    == Evm.Ok{value, Evm.State{Evm.Slot{Evm.Plain{0n}, value} <> storage, 7n, limit, logs}} : Evm.Outcome<Nat>}

law decrement_at_zero:
  for storage: List<&2, Evm.Slot>
  for who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  {Counter.decrement(Evm.State{Evm.Slot{Evm.Plain{0n}, 0n} <> storage, who, limit, logs}) == Evm.Revert{} : Evm.Outcome<Unit>}
