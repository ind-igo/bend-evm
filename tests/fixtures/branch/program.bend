import Base
import ../../../src/Evm.bend as Evm

# Branches: each arm runs to the end of the call.

# Stores x at slot 0 only when it is not zero; returns 1 when it stored.
def keep(+x: Nat) -> Evm.Contract(Nat):
  Evm.branch(Nat.is_eq(x, 0n), Nat, Evm.Contract.pure(Nat, 0n),
    do Evm.Contract<Nat>:
      Evm.sstore(0n, x)
      Evm.Contract.pure(Nat, 1n))

# A chain: 0 for x < 10, 1 for x < 100, else x - 100.
def grade(+x: Nat) -> Evm.Contract(Nat):
  Evm.branch(Nat.is_lt(x, 10n), Nat, Evm.Contract.pure(Nat, 0n),
    Evm.branch(Nat.is_lt(x, 100n), Nat, Evm.Contract.pure(Nat, 1n), Evm.sub(x, 100n)))

def get() -> Evm.Contract(Nat):
  Evm.sload(0n)
