import Base
import ../../../src/Evm.bend as Evm
import ./program.bend as Branch

# Each arm gives its own outcome, from any state. The last arm of grade keeps
# the check of Evm.sub, which cannot fail there.

law keep:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for +x: Nat
  {Evm.run(Nat, Branch.keep(x), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Nat>, Nat.is_eq(x, 0n),
      Evm.Ok{0n, Evm.State{storage, who, limit, logs, world}},
      Evm.Ok{1n, Evm.State{Evm.Slot{Evm.Plain{0n}, x} <> storage, who, limit, logs, world}}) : Evm.Outcome<Nat>}

law grade:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for +x: Nat
  {Evm.run(Nat, Branch.grade(x), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(x, 10n), Evm.Ok{0n, Evm.State{storage, who, limit, logs, world}},
      Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(x, 100n), Evm.Ok{1n, Evm.State{storage, who, limit, logs, world}},
        Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(x, 100n), Evm.Revert{},
          Evm.Ok{Nat.sub(x, 100n), Evm.State{storage, who, limit, logs, world}}))) : Evm.Outcome<Nat>}
