import Base
import ../../../src/Evm.bend as Evm

# View calls that compile rejects.

# A call without an interface def.
def bare() -> Evm.Contract(Nat):
  Evm.view(Evm.Call{0n, "f", []})

# A call has no topics.
def marked(token: Evm.Address, x: Evm.Indexed(Nat)) -> Evm.Call:
  Evm.Call{token, "marked", [x]}

def topic() -> Evm.Contract(Nat):
  Evm.view(marked(0n, 1n))

# Two calls with one name but other argument types. The target is not in
# the signature, so the error names peek(uint256).
def peek(token: Evm.Address, x: Nat) -> Evm.Call:
  Evm.Call{token, "peek", [x]}

def other.peek(token: Nat, who: Evm.Address) -> Evm.Call:
  Evm.Call{token, "peek", [who]}

def peeks() -> Evm.Contract(Nat):
  Evm.view(peek(0n, 1n))
