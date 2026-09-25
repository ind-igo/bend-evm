import Base
import ../../../src/Evm.bend as Evm
import ./program.bend as Branch

# Branches that compile must reject.

# A branch that is not the last step.
def early(+x: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    y : Nat <- Evm.branch(Nat.is_eq(x, 0n), Nat, Evm.Contract.pure(Nat, 0n), Evm.Contract.pure(Nat, 1n))
    Evm.Contract.pure(Nat, y)

# A call to a function that branches, before the last step.
def middle(+x: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    y : Nat <- Branch.keep(x)
    Evm.Contract.pure(Nat, y)
