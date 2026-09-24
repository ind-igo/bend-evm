import Base
import ../../src/Evm.bend as Evm

# Constructors that compile must reject.

def init(x: Nat) -> Evm.Contract(Unit):
  Evm.sstore(0n, x)

def get() -> Evm.Contract(Nat):
  Evm.sload(0n)
