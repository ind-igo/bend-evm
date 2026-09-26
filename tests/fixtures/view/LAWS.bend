import Base
import ../../../src/Evm.bend as Evm
import ./program.bend as Program

# others takes the next two answers, in order, and reverts unless each one
# answers its call. It changes no storage.

law others:
  for storage: List<&2, Evm.Slot>
  for who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for time: Nat
  for chain: Nat
  for self: Nat
  for hashes: List<&2, Evm.Hashed>
  for signers: List<&2, Evm.Signed>
  for q: Evm.Call
  for +held: Nat
  for r: Evm.Call
  for +supply: Nat
  for rest: List<&2, Evm.Answer>
  for +token: Nat
  for +owner: Nat
  {Evm.run(Nat, Program.others(token, owner), Evm.State{storage, who, limit, logs,
      Evm.World{time, chain, self, hashes, signers, Evm.Answer{q, held} <> Evm.Answer{r, supply} <> rest}})
    == Bool.pick(Evm.Outcome<Nat>, Evm.same.call(q, Evm.Call{token, "balanceOf", [owner]}),
      Bool.pick(Evm.Outcome<Nat>, Evm.same.call(r, Evm.Call{token, "totalSupply", []}),
        Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(supply, held), Evm.Revert{},
          Evm.Ok{Nat.sub(supply, held), Evm.State{storage, who, limit, logs, Evm.World{time, chain, self, hashes, signers, rest}}}),
        Evm.Revert{}),
      Evm.Revert{}) : Evm.Outcome<Nat>}
