import Base
import ../../src/Evm.bend as Evm

# The calls that the pair makes to its two tokens.

def balanceOf(token: Evm.Address, who: Evm.Address) -> Evm.Call:
  Evm.Call{token, "balanceOf", [who]}

def transfer(token: Evm.Address, to: Evm.Address, amount: Nat) -> Evm.Call:
  Evm.Call{token, "transfer", [to, amount]}
