import Base
import ../../../src/Evm.bend as Evm

# A reentrancy guard in transient storage, after solady's
# ReentrancyGuardTransient, for tests/transient.test.js. poke counts, then
# calls ping() on a target, which returns a word, with the lock set; a callback into poke while
# the lock is set reverts with Reentrancy().

def LOCK() -> Nat:
  0n

def COUNT() -> Nat:
  0n

def Reentrancy() -> Evm.Error:
  Evm.Error{"Reentrancy", []}

def ping(target: Evm.Address) -> Evm.Call:
  Evm.Call{target, "ping", []}

def enter() -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    held : Nat <- Evm.tload(LOCK())
    Evm.ensure(Nat.is_eq(held, 0n), Reentrancy())
    Evm.tstore(LOCK(), 1n)

def leave() -> Evm.Contract(Unit):
  Evm.tstore(LOCK(), 0n)

def poke(+target: Evm.Address) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    enter()
    n : Nat <- Evm.sload(COUNT())
    m : Nat <- Evm.add(n, 1n)
    Evm.sstore(COUNT(), m)
    _ : Nat <- Evm.call(ping(target))
    leave()

def count() -> Evm.Contract(Nat):
  Evm.sload(COUNT())

def locked() -> Evm.Contract(Nat):
  Evm.tload(LOCK())
