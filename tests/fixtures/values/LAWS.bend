import Base
import ../../../src/Evm.bend as Evm
import ./program.bend as Program

# reserves gives the first two words of the target's getReserves(), each an
# answer for the same call, from any state.
law reserves:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +facts: List<&2, Evm.Fact>
  for +readings: List<&2, Nat>
  for +self: Nat
  for +hashes: List<&2, Evm.Hashed>
  for +signers: List<&2, Evm.Signed>
  for +q0: Evm.Call
  for +a: Nat
  for +q1: Evm.Call
  for +b: Nat
  for +more: List<&2, Evm.Answer>
  for +target: Nat
  {Evm.run(Evm.Values, Program.reserves(target), Evm.State{storage, who, limit, logs,
      Evm.World{facts, readings, self, hashes, signers, Evm.Answer{q0, a} <> Evm.Answer{q1, b} <> more}})
    == Bool.pick(Evm.Outcome<Evm.Values>, Evm.same.call(q0, Evm.Call{target, "getReserves", []}),
      Bool.pick(Evm.Outcome<Evm.Values>, Evm.same.call(q1, Evm.Call{target, "getReserves", []}),
        Evm.Ok{Evm.Values{[a, b]}, Evm.State{storage, who, limit, logs, Evm.World{facts, readings, self, hashes, signers, more}}},
        Evm.Revert{}),
      Evm.Revert{}) : Evm.Outcome<Evm.Values>}
