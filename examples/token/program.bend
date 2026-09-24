import Base
import ../../src/Evm.bend as Evm

# A minimal token. Slot 0 holds the total supply, and the mapping at slot 1
# holds balances. Results are words, so `true` is the word 1.

def owner() -> Nat:
  7n

def transfer_event() -> String:
  "Transfer(address,address,uint256)"

def totalSupply() -> Evm.Contract(Nat):
  Evm.sload(0n)

def balanceOf(who: Evm.Address) -> Evm.Contract(Nat):
  Evm.load(1n, who)

def transfer(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +sender : Nat <- Evm.caller()
    a : Nat <- Evm.load(1n, sender)
    rest : Nat <- Evm.sub(a, amount)
    Evm.store(1n, sender, rest)
    b : Nat <- Evm.load(1n, to)
    sum : Nat <- Evm.add(b, amount)
    Evm.store(1n, to, sum)
    Evm.log(transfer_event(), [sender, to], amount)
    Evm.Contract.pure(Nat, 1n)

def mint(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    who : Nat <- Evm.caller()
    Evm.require(Nat.is_eq(who, owner()))
    supply : Nat <- Evm.sload(0n)
    total : Nat <- Evm.add(supply, amount)
    Evm.sstore(0n, total)
    b : Nat <- Evm.load(1n, to)
    sum : Nat <- Evm.add(b, amount)
    Evm.store(1n, to, sum)
    Evm.log(transfer_event(), [0n, to], amount)
