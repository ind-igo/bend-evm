import Base
import ../../src/Evm.bend as Evm

# Constant strings and small ABI types.

def name() -> String:
  "Bend Token"

def symbol() -> String:
  "A symbol that is longer than one word of thirty-two bytes"

def decimals() -> Evm.Contract(Evm.Uint8):
  Evm.Contract.pure(Nat, 18n)

def echo(x: Evm.Uint8, flag: Evm.Boolean) -> Evm.Contract(Nat):
  Evm.add(x, flag)

# With "()", its signature has 136 bytes, which one Keccak block cannot hold.
def aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa() -> String:
  "long"

# A constant string cannot be the constructor.
def init() -> String:
  "init"
