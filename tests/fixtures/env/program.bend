import Base
import ../../../src/Evm.bend as Evm

# One entry for each value of the environment, for tests/fixtures/env.test.js,
# and block, which logs the values of the block and the transaction.

def timestamp() -> Evm.Contract(Nat):
  Evm.timestamp()

def chainid() -> Evm.Contract(Nat):
  Evm.chainid()

def origin() -> Evm.Contract(Nat):
  Evm.origin()

def gasprice() -> Evm.Contract(Nat):
  Evm.gasprice()

def coinbase() -> Evm.Contract(Nat):
  Evm.coinbase()

def number() -> Evm.Contract(Nat):
  Evm.number()

def prevrandao() -> Evm.Contract(Nat):
  Evm.prevrandao()

def gaslimit() -> Evm.Contract(Nat):
  Evm.gaslimit()

def basefee() -> Evm.Contract(Nat):
  Evm.basefee()

def blobbasefee() -> Evm.Contract(Nat):
  Evm.blobbasefee()

def codesize() -> Evm.Contract(Nat):
  Evm.codesize()

def gas() -> Evm.Contract(Nat):
  Evm.gas()

def selfbalance() -> Evm.Contract(Nat):
  Evm.selfbalance()

def blockhash(n: Nat) -> Evm.Contract(Nat):
  Evm.blockhash(n)

def blobhash(i: Nat) -> Evm.Contract(Nat):
  Evm.blobhash(i)

def balance(a: Nat) -> Evm.Contract(Nat):
  Evm.balance(a)

def extcodesize(a: Nat) -> Evm.Contract(Nat):
  Evm.extcodesize(a)

def extcodehash(a: Nat) -> Evm.Contract(Nat):
  Evm.extcodehash(a)

def Block(timestamp: Nat, number: Nat, coinbase: Nat, prevrandao: Nat, gaslimit: Nat, basefee: Nat, blobbasefee: Nat,
  gasprice: Nat, origin: Nat) -> Evm.Log:
  Evm.Log{"Block", [], [timestamp, number, coinbase, prevrandao, gaslimit, basefee, blobbasefee, gasprice, origin]}

def block() -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    t : Nat <- Evm.timestamp()
    n : Nat <- Evm.number()
    c : Nat <- Evm.coinbase()
    r : Nat <- Evm.prevrandao()
    l : Nat <- Evm.gaslimit()
    b : Nat <- Evm.basefee()
    x : Nat <- Evm.blobbasefee()
    p : Nat <- Evm.gasprice()
    o : Nat <- Evm.origin()
    Evm.emit(Block(t, n, c, r, l, b, x, p, o))
