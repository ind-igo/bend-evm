import Base
import ../../../src/Evm.bend as Evm

# Events that the reader must reject.

def Late(amount: Nat, from: Evm.Indexed(Evm.Address)) -> Evm.Event:
  Evm.Log{"Late(uint256,address)", [from], [amount]}

def Wide(a: Evm.Indexed(Nat), b: Evm.Indexed(Nat), c: Evm.Indexed(Nat), d: Evm.Indexed(Nat)) -> Evm.Event:
  Evm.Log{"Wide(uint256,uint256,uint256,uint256)", [a, b, c, d], []}

# An indexed field after a data field.
def late() -> Evm.Contract(Unit):
  Evm.emit(Late(1n, 2n))

# Four indexed fields.
def wide() -> Evm.Contract(Unit):
  Evm.emit(Wide(1n, 2n, 3n, 4n))

# A def that returns a log but is not marked as an event.
def Plain(x: Nat) -> Evm.Log:
  Evm.Log{"Plain(uint256)", [], [x]}

def plain() -> Evm.Contract(Unit):
  Evm.emit(Plain(1n))

# A log without an event def.
def raw() -> Evm.Contract(Unit):
  Evm.emit(Evm.Log{"E(uint256)", [], [0n]})
