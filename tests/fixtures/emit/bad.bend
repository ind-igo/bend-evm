import Base
import ../../../src/Evm.bend as Evm

# Events that the reader must reject.

type Events is Data:
  Late{amount: Nat, from: Evm.Indexed(Evm.Address)}
  Wide{a: Evm.Indexed(Nat), b: Evm.Indexed(Nat), c: Evm.Indexed(Nat), d: Evm.Indexed(Nat)}

def log(e: Events) -> Evm.Log:
  match e:
    case Late{amount, from}:
      Evm.Log{"Late(uint256,address)", [from], [amount]}
    case Wide{a, b, c, d}:
      Evm.Log{"Wide(uint256,uint256,uint256,uint256)", [a, b, c, d], []}

# An indexed field after a data field.
def late() -> Evm.Contract(Unit):
  Evm.emit(log(Late{1n, 2n}))

# Four indexed fields.
def wide() -> Evm.Contract(Unit):
  Evm.emit(log(Wide{1n, 2n, 3n, 4n}))

# A log without an event constructor.
def raw() -> Evm.Contract(Unit):
  Evm.emit(Evm.Log{"E(uint256)", [], [0n]})
