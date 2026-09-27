import Base
import ../../../src/Evm.bend as Evm
import ./IToken.bend as IToken

# A vault for one ERC-20 token, with one share for each unit it holds. Each
# entry updates the shares before it calls the token, so a token that calls
# back sees the shares that match the call.

def init(+token: Evm.Address) -> Evm.Contract(Unit):
  Evm.sstore(2n, token)

def token() -> Evm.Contract(Nat):
  Evm.sload(2n)

def sharesOf(who: Evm.Address) -> Evm.Contract(Nat):
  Evm.load(0n, who)

def totalShares() -> Evm.Contract(Nat):
  Evm.sload(1n)

# Gives the caller amount shares, then takes amount tokens from the caller.
def deposit(+amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    +held : Nat <- Evm.load(0n, who)
    +more : Nat <- Evm.add(held, amount)
    +total : Nat <- Evm.sload(1n)
    +sum : Nat <- Evm.add(total, amount)
    +token : Nat <- Evm.sload(2n)
    +me : Nat <- Evm.self()
    Evm.store(0n, who, more)
    Evm.sstore(1n, sum)
    ok : Nat <- Evm.call(IToken.transferFrom(token, who, me, amount))
    Evm.require(Nat.is_eq(ok, 1n))

# Takes amount shares from the caller, then sends the caller amount tokens.
def withdraw(+amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    +held : Nat <- Evm.load(0n, who)
    +less : Nat <- Evm.sub(held, amount)
    +total : Nat <- Evm.sload(1n)
    +rest : Nat <- Evm.sub(total, amount)
    +token : Nat <- Evm.sload(2n)
    Evm.store(0n, who, less)
    Evm.sstore(1n, rest)
    ok : Nat <- Evm.call(IToken.transfer(token, who, amount))
    Evm.require(Nat.is_eq(ok, 1n))

# The word that the token's ping gives for x: a call as the last step.
def ping(+x: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +token : Nat <- Evm.sload(2n)
    Evm.call(IToken.ping(token, x))
