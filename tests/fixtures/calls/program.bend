import Base
import ../../../src/Evm.bend as Evm

# Calls between contract functions, one for each way the reader joins a
# callee to its caller.

def seven() -> Evm.Contract(Nat):
  Evm.Contract.pure(Nat, 7n)

def twice(+x: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    y : Nat <- Evm.add(x, x)
    Evm.Contract.pure(Nat, y)

def put(slot: Nat, value: Nat) -> Evm.Contract(Unit):
  Evm.sstore(slot, value)

def keep(+v: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    put(1n, v)
    Evm.sload(1n)

def run(+a: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    s : Nat <- seven()
    t : Nat <- twice(a)
    +u : Nat <- twice(t)
    put(0n, u)
    v : Nat <- Evm.add(s, u)
    keep(v)
