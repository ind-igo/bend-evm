import Base
import ../../../src/Evm.bend as Evm

# A call that compile rejects: it has no interface def.
def bare() -> Evm.Contract(Nat):
  Evm.call(Evm.Call{0n, "f", []})
