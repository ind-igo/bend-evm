import Base
import ../../../src/Evm.bend as Evm

# Several words, for tests/values.test.js: a function that returns a tuple,
# and view calls that give several words or fail.

def Reserves(reserve0: Nat, reserve1: Nat) -> Evm.Values:
  Evm.Values{[reserve0, reserve1]}

def getReserves(target: Evm.Address) -> Evm.Call:
  Evm.Call{target, "getReserves", []}

def fail(target: Evm.Address) -> Evm.Call:
  Evm.Call{target, "fail", []}

# The first two words of target's getReserves().
def reserves(+target: Evm.Address) -> Evm.Contract(Evm.Values):
  do Evm.Contract<Evm.Values>:
    +v : Evm.Values <- Evm.views(getReserves(target), 2n)
    Evm.Contract.pure(Evm.Values, Reserves(Evm.item(v, 0n), Evm.item(v, 1n)))

def total(+target: Evm.Address) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +v : Evm.Values <- Evm.views(getReserves(target), 3n)
    Evm.unchecked.add(Evm.item(v, 0n), Evm.item(v, 2n))

# Reverts with the data of target's failed fail().
def failing(+target: Evm.Address) -> Evm.Contract(Nat):
  Evm.view(fail(target))
