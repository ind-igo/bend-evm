import Base
import ../../../src/Evm.bend as Evm

# A typed event: the reader takes the signature and the topic from the
# field types, and the certificate checks the encoder against them.

type Events is Data:
  Moved{from: Evm.Indexed(Evm.Address), amount: Nat}

def log(e: Events) -> Evm.Log:
  match e:
    case Moved{from, amount}:
      Evm.Log{"Moved(address,uint256)", [from], [amount]}

def moved(+amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    Evm.emit(log(Moved{who, amount}))
