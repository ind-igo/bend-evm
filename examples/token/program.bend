import Base
import ../../src/Evm.bend as Evm

# A minimal ERC-20 token. Slot 0 holds the total supply, the mapping at slot 1
# holds balances, the mapping at slot 2 holds, for each holder, the allowance
# of each spender, and slot 3 holds the owner, who can mint. Results are
# words, so `true` is the word 1.

def transfer_event() -> String:
  "Transfer(address,address,uint256)"

def approval_event() -> String:
  "Approval(address,address,uint256)"

def ownership_event() -> String:
  "OwnershipTransferred(address,address)"

# The constructor: the deployer is the owner.
def init() -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    Evm.sstore(3n, who)
    Evm.log(ownership_event(), [0n, who], [])

def owner() -> Evm.Contract(Nat):
  Evm.sload(3n)

def transferOwnership(+next: Evm.Address) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    who : Nat <- Evm.caller()
    +boss : Nat <- Evm.sload(3n)
    Evm.require(Nat.is_eq(who, boss))
    Evm.sstore(3n, next)
    Evm.log(ownership_event(), [boss, next], [])

def totalSupply() -> Evm.Contract(Nat):
  Evm.sload(0n)

def balanceOf(who: Evm.Address) -> Evm.Contract(Nat):
  Evm.load(1n, who)

def transfer(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +sender : Nat <- Evm.caller()
    a : Nat <- Evm.load(1n, sender)
    rest : Nat <- Evm.sub(a, amount)
    Evm.store(1n, sender, rest)
    b : Nat <- Evm.load(1n, to)
    sum : Nat <- Evm.add(b, amount)
    Evm.store(1n, to, sum)
    Evm.log(transfer_event(), [sender, to], [amount])
    Evm.Contract.pure(Nat, 1n)

def mint(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    who : Nat <- Evm.caller()
    boss : Nat <- Evm.sload(3n)
    Evm.require(Nat.is_eq(who, boss))
    supply : Nat <- Evm.sload(0n)
    total : Nat <- Evm.add(supply, amount)
    Evm.sstore(0n, total)
    b : Nat <- Evm.load(1n, to)
    sum : Nat <- Evm.add(b, amount)
    Evm.store(1n, to, sum)
    Evm.log(transfer_event(), [0n, to], [amount])

def allowance(holder: Evm.Address, spender: Evm.Address) -> Evm.Contract(Nat):
  Evm.load2(2n, holder, spender)

def approve(+spender: Evm.Address, +amount: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +holder : Nat <- Evm.caller()
    Evm.store2(2n, holder, spender, amount)
    Evm.log(approval_event(), [holder, spender], [amount])
    Evm.Contract.pure(Nat, 1n)

# The caller spends from the allowance that `from` gave it. An allowance of
# max() is unlimited and does not go down.
def transferFrom(+from: Evm.Address, +to: Evm.Address, +amount: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +spender : Nat <- Evm.caller()
    +allowed : Nat <- Evm.load2(2n, from, spender)
    top : Nat <- Evm.max()
    spend : Nat <- Evm.select(Nat.is_eq(allowed, top), 0n, amount)
    left : Nat <- Evm.sub(allowed, spend)
    Evm.store2(2n, from, spender, left)
    a : Nat <- Evm.load(1n, from)
    rest : Nat <- Evm.sub(a, amount)
    Evm.store(1n, from, rest)
    b : Nat <- Evm.load(1n, to)
    sum : Nat <- Evm.add(b, amount)
    Evm.store(1n, to, sum)
    Evm.log(transfer_event(), [from, to], [amount])
    Evm.Contract.pure(Nat, 1n)
