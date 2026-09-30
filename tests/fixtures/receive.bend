import Base
import ../../src/Evm.bend as Evm

# A receive that is not payable, which compile rejects.
def receive() -> Evm.Contract(Unit):
  Evm.sstore(0n, 1n)
