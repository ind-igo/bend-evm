import Base
import ../../../src/Evm.bend as Evm

# The calls that the vault makes to its token.

def transfer(token: Evm.Address, to: Evm.Address, amount: Nat) -> Evm.Call:
  Evm.Call{token, "transfer", [to, amount]}

def transferFrom(token: Evm.Address, from: Evm.Address, to: Evm.Address, amount: Nat) -> Evm.Call:
  Evm.Call{token, "transferFrom", [from, to, amount]}

def ping(token: Evm.Address, x: Nat) -> Evm.Call:
  Evm.Call{token, "ping", [x]}
