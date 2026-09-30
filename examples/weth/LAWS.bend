import Base
import ../../src/Evm.bend as Evm
import ./WETH.bend as WETH

# The laws of wrapped ether (WETH.bend). Each gives every outcome from any
# state. The ERC20 core's laws (examples/erc20/LAWS.bend) cover the other
# functions. Slot 0 holds the total supply and the mapping at slot 1 holds
# balances. Storage is newest first, so new slots shadow old ones.

def supply(storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{0n})

def balance(storage: List<&2, Evm.Slot>, who: Nat) -> Nat:
  Evm.lookup(storage, Evm.Mapped{Evm.Plain{1n}, who})

def minted(+storage: List<&2, Evm.Slot>, +to: Nat, +amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(balance(storage, to), amount)}
    <> Evm.Slot{Evm.Plain{0n}, Nat.add(supply(storage), amount)} <> storage

def burned(+storage: List<&2, Evm.Slot>, +from: Nat, +amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Plain{0n}, Nat.sub(supply(storage), amount)}
    <> Evm.Slot{Evm.Mapped{Evm.Plain{1n}, from}, Nat.sub(balance(storage, from), amount)} <> storage

# A deposit of the value sent: the first reading, which callvalue uses up.
def deposited(+storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +facts: List<&2, Evm.Fact>,
  +value: Nat, +readings: List<&2, Nat>, +self: Nat, +hashes: List<&2, Evm.Hashed>, +signers: List<&2, Evm.Signed>,
  +answers: List<&2, Evm.Answer>) -> Evm.Outcome<Unit>:
  Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(supply(storage), value), limit),
    Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(balance(storage, who), value), limit),
      Evm.Ok{Unit{}, Evm.State{minted(storage, who, value), who, limit,
        Evm.Log{"Deposit", [who], [value]} <> Evm.Log{"Transfer", [0n, who], [value]} <> logs,
        Evm.World{facts, readings, self, hashes, signers, answers}}},
      Evm.Revert{}),
    Evm.Revert{})

# A deposit gives the sender as many tokens as the wei it sent; it reverts
# only where the supply would overflow.
law deposit:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +facts: List<&2, Evm.Fact>
  for +value: Nat
  for +readings: List<&2, Nat>
  for +self: Nat
  for +hashes: List<&2, Evm.Hashed>
  for +signers: List<&2, Evm.Signed>
  for +answers: List<&2, Evm.Answer>
  {Evm.run(Unit, WETH.deposit(), Evm.State{storage, who, limit, logs,
      Evm.World{facts, value <> readings, self, hashes, signers, answers}})
    == deposited(storage, who, limit, logs, facts, value, readings, self, hashes, signers, answers) : Evm.Outcome<Unit>}

# Ether sent with no calldata is the same deposit.
law receive:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +facts: List<&2, Evm.Fact>
  for +value: Nat
  for +readings: List<&2, Nat>
  for +self: Nat
  for +hashes: List<&2, Evm.Hashed>
  for +signers: List<&2, Evm.Signed>
  for +answers: List<&2, Evm.Answer>
  {Evm.run(Unit, WETH.receive(), Evm.State{storage, who, limit, logs,
      Evm.World{facts, value <> readings, self, hashes, signers, answers}})
    == deposited(storage, who, limit, logs, facts, value, readings, self, hashes, signers, answers) : Evm.Outcome<Unit>}

# A withdrawal reverts unless the sender's balance covers the amount. Else
# it burns the tokens and logs, and only then sends the wei, as its last
# step: the receiver may call back, but it sees the burned balance, and
# the withdrawal does nothing after it.
law withdraw:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +amount: Nat
  {Evm.run(Unit, WETH.withdraw(amount), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(balance(storage, who), amount),
      Evm.Revert{},
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(supply(storage), amount),
        Evm.Revert{},
        Evm.Calling{Evm.Pay{who, amount}, Evm.State{burned(storage, who, amount), who, limit,
          Evm.Log{"Withdrawal", [who], [amount]} <> Evm.Log{"Transfer", [who, 0n], [amount]} <> logs, world},
          _ => t => Evm.Ok{Unit{}, t}})) : Evm.Outcome<Unit>}
