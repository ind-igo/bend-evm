import Base
import ../../../src/Evm.bend as Evm

# Entries that compile rejects.

# A call without an interface def.
def bare() -> Evm.Contract(Nat):
  Evm.call(Evm.Call{0n, "f", []})

# An entry whose name is not an identifier.
def dotted.entry() -> Evm.Contract(Nat):
  Evm.sload(0n)
