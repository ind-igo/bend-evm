import Base
import ../../src/Evm.bend as Evm
import ./program.bend as Token

# Account 8 sends to account 9, and the owner is 7. Balances, amounts, the
# rest of storage, the word limit and earlier logs stay symbolic. Storage is
# newest first, so new slots shadow old ones; transfer adds no plain slot, so
# totalSupply (plain slot 0) does not change.

law transfer_moves:
  for storage: List<&2, Evm.Slot>
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for +a: Nat
  for +b: Nat
  for +amount: Nat
  for enough: {False{} == Nat.is_lt(a, amount) : Bool}
  for fits: {True{} == Nat.is_lt(Nat.add(b, amount), limit) : Bool}
  {Token.transfer(9n, amount,
      Evm.State{Evm.Slot{Evm.Mapped{1n, 8n}, a} <> Evm.Slot{Evm.Mapped{1n, 9n}, b} <> storage, 8n, limit, logs})
    == Evm.Ok{1n, Evm.State{Evm.Slot{Evm.Mapped{1n, 9n}, Nat.add(b, amount)}
      <> Evm.Slot{Evm.Mapped{1n, 8n}, Nat.sub(a, amount)}
      <> Evm.Slot{Evm.Mapped{1n, 8n}, a} <> Evm.Slot{Evm.Mapped{1n, 9n}, b} <> storage, 8n, limit,
      Evm.Log{"Transfer(address,address,uint256)", [8n, 9n], amount} <> logs}} : Evm.Outcome<Nat>}

law transfer_short:
  for storage: List<&2, Evm.Slot>
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for +a: Nat
  for b: Nat
  for +amount: Nat
  for short: {True{} == Nat.is_lt(a, amount) : Bool}
  {Token.transfer(9n, amount,
      Evm.State{Evm.Slot{Evm.Mapped{1n, 8n}, a} <> Evm.Slot{Evm.Mapped{1n, 9n}, b} <> storage, 8n, limit, logs})
    == Evm.Revert{} : Evm.Outcome<Nat>}

law mint_by_owner:
  for storage: List<&2, Evm.Slot>
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for +supply: Nat
  for +b: Nat
  for +amount: Nat
  for room: {True{} == Nat.is_lt(Nat.add(supply, amount), limit) : Bool}
  for fits: {True{} == Nat.is_lt(Nat.add(b, amount), limit) : Bool}
  {Token.mint(9n, amount,
      Evm.State{Evm.Slot{Evm.Plain{0n}, supply} <> Evm.Slot{Evm.Mapped{1n, 9n}, b} <> storage, 7n, limit, logs})
    == Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Mapped{1n, 9n}, Nat.add(b, amount)}
      <> Evm.Slot{Evm.Plain{0n}, Nat.add(supply, amount)}
      <> Evm.Slot{Evm.Plain{0n}, supply} <> Evm.Slot{Evm.Mapped{1n, 9n}, b} <> storage, 7n, limit,
      Evm.Log{"Transfer(address,address,uint256)", [0n, 9n], amount} <> logs}} : Evm.Outcome<Unit>}

law mint_by_other:
  for storage: List<&2, Evm.Slot>
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for to: Nat
  for amount: Nat
  {Token.mint(to, amount, Evm.State{storage, 8n, limit, logs}) == Evm.Revert{} : Evm.Outcome<Unit>}
