import Base
import ../../../src/Evm.bend as Evm

# An event def and an error def: the reader takes the signature, and the
# event's topic, from the parameter types, and the certificate checks each
# body against them.

def Moved(from: Evm.Indexed(Evm.Address), amount: Nat) -> Evm.Event:
  Evm.Log{"Moved(address,uint256)", [from], [amount]}

def TooSmall(amount: Nat, least: Nat) -> Evm.Error:
  Evm.Error{"TooSmall(uint256,uint256)", [amount, least]}

def moved(+amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    Evm.emit(Moved(who, amount))

# Moves at least 10, or reverts with TooSmall.
def take(+amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    Evm.ensure(Bool.not(Nat.is_lt(amount, 10n)), TooSmall(amount, 10n))
    moved(amount)
