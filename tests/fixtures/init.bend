import Base
import ../../src/Evm.bend as Evm

# Entries that compile must reject.

def init(x: Nat) -> Evm.Contract(Nat):
  Evm.sload(x)

def get() -> Evm.Contract(Nat):
  Evm.sload(0n)

# A slot from a parameter could alias a mapping entry on chain.
def poke(x: Nat, v: Nat) -> Evm.Contract(Unit):
  Evm.sstore(x, v)

# Not a contract function.
def plain(x: Nat) -> Nat:
  x
