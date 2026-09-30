import Base
import ../../../src/Evm.bend as Evm
import ./program.bend as Program

# The laws of the guard. The two together say that a callback into poke
# while its call runs raises Reentrancy(): the call runs with the lock set,
# and a poke with the lock set raises.

def lock(storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Transient{0n})

def count(storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{0n})

# A poke with the lock clear: it counts, sets the lock, and calls ping on
# the target; when the call returns, it clears the lock.
def poked(+storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World, +target: Nat) ->
  Evm.Outcome<Unit>:
  Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(count(storage), 1n), limit),
    Evm.Calling{Evm.Call{target, "ping", []},
      Evm.State{Evm.Slot{Evm.Plain{0n}, Nat.add(count(storage), 1n)} <> Evm.Slot{Evm.Transient{0n}, 1n} <> storage, who, limit, logs, world},
      _ => t => Evm.Ok{Unit{}, Evm.write.go(Evm.Transient{0n}, 0n, t)}},
    Evm.Revert{})

law poke:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +target: Nat
  for +h: {True{} == Nat.is_eq(lock(storage), 0n) : Bool}
  {Evm.run(Unit, Program.poke(target), Evm.State{storage, who, limit, logs, world})
    == poked(storage, who, limit, logs, world, target) : Evm.Outcome<Unit>}

law reentered:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +target: Nat
  for +h: {False{} == Nat.is_eq(lock(storage), 0n) : Bool}
  {Evm.run(Unit, Program.poke(target), Evm.State{storage, who, limit, logs, world})
    == Evm.Raise{Program.Reentrancy()} : Evm.Outcome<Unit>}
