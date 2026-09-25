import Base
import ../../src/Evm.bend as Evm

# A counter at slot 0 that anyone can move by one and only the owner can set.
def COUNT() -> Nat:
  0n

def OWNER() -> Nat:
  7n

def get() -> Evm.Contract(Nat):
  Evm.sload(COUNT())

def increment() -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    n : Nat <- Evm.sload(COUNT())
    m : Nat <- Evm.add(n, 1n)
    Evm.sstore(COUNT(), m)

def decrement() -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    n : Nat <- Evm.sload(COUNT())
    m : Nat <- Evm.sub(n, 1n)
    Evm.sstore(COUNT(), m)

def set(value: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    who : Nat <- Evm.caller()
    Evm.require(Nat.is_eq(who, OWNER()))
    Evm.sstore(COUNT(), value)
