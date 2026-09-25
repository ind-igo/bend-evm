import Base
import ../../../src/Evm.bend as Evm

# An event def: the reader takes the signature and the topic from the
# parameter types, and the certificate checks the body against them.

def Moved(from: Evm.Indexed(Evm.Address), amount: Nat) -> Evm.Event:
  Evm.Log{"Moved(address,uint256)", [from], [amount]}

def moved(+amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    Evm.emit(Moved(who, amount))
