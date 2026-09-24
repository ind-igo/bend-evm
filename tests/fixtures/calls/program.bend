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

# A callee whose body is only a call: its callee's locals must not take the
# levels of its own parameters.
def inc(a: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    x : Nat <- Evm.load(1n, a)
    Evm.add(x, 1n)

def wide(a: Nat, b: Nat, c: Nat, d: Nat, e: Nat) -> Evm.Contract(Nat):
  inc(a)

def outer(p: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    r : Nat <- wide(p, 0n, 0n, 9n, 0n)
    Evm.Contract.pure(Nat, r)
