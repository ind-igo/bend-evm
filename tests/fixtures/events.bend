import Base
import ../../src/Evm.bend as Evm

# Events that the reader must reject.

def quoted() -> Evm.Contract(Unit):
  Evm.log("E(uint256)\" law", [], 0n)

def wide() -> Evm.Contract(Unit):
  Evm.log("E(uint256,uint256,uint256,uint256)", [1n, 2n, 3n, 4n], 0n)
