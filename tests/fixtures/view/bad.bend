import Base
import ../../../src/Evm.bend as Evm

# View calls that compile rejects.

# A call without an interface def.
def bare() -> Evm.Contract(Nat):
  Evm.view(Evm.Call{0n, "f()", []})

# A call has no topics.
def marked(token: Evm.Address, x: Evm.Indexed(Nat)) -> Evm.Call:
  Evm.Call{token, "marked(uint256)", [x]}

def topic() -> Evm.Contract(Nat):
  Evm.view(marked(0n, 1n))
