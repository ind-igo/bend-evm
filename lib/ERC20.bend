import Base
import ../src/Evm.bend as Evm

# An ERC-20 base, after solmate's ERC20. A token imports it, defines name(),
# symbol() and decimals(), and exposes each standard function with a
# one-line def that calls this base; mint and burn are internal, like
# solmate's _mint and _burn. See examples/token.
#
# Storage: slot 0 holds the total supply, the mapping at slot 1 the balances,
# and the mapping at slot 2, for each owner, the allowance of each spender. A
# token keeps its own state from slot 3 on.
#
# As in solmate, transfers need no zero-address checks, and an allowance of
# the largest word is unlimited. Unlike solmate, the receiver's add is
# checked. It cannot fail, because no balance exceeds the total supply (the
# token's supply_sum law), but the check costs a little gas.

def transfer_event() -> String:
  "Transfer(address,address,uint256)"

def approval_event() -> String:
  "Approval(address,address,uint256)"

def totalSupply() -> Evm.Contract(Nat):
  Evm.sload(0n)

def balanceOf(who: Evm.Address) -> Evm.Contract(Nat):
  Evm.load(1n, who)

def allowance(owner: Evm.Address, spender: Evm.Address) -> Evm.Contract(Nat):
  Evm.load2(2n, owner, spender)

def approve(+spender: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  do Evm.Contract<Nat>:
    +owner : Nat <- Evm.caller()
    Evm.store2(2n, owner, spender, amount)
    Evm.log(approval_event(), [owner, spender], [amount])
    Evm.Contract.pure(Nat, 1n)

# Adds amount to the balance of to.
def credit(+to: Nat, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    b : Nat <- Evm.load(1n, to)
    sum : Nat <- Evm.add(b, amount)
    Evm.store(1n, to, sum)

# Moves amount from one balance to another and logs it.
def move(+from: Nat, +to: Nat, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    a : Nat <- Evm.load(1n, from)
    rest : Nat <- Evm.sub(a, amount)
    Evm.store(1n, from, rest)
    credit(to, amount)
    Evm.log(transfer_event(), [from, to], [amount])

def transfer(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  do Evm.Contract<Nat>:
    sender : Nat <- Evm.caller()
    move(sender, to, amount)
    Evm.Contract.pure(Nat, 1n)

# What transferFrom takes from an allowance: nothing when it is the largest
# word, which is unlimited.
def spent(+allowed: Nat, +amount: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    top : Nat <- Evm.max()
    Evm.select(Nat.is_eq(allowed, top), 0n, amount)

# The caller spends from the allowance that `from` gave it.
def transferFrom(+from: Evm.Address, +to: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  do Evm.Contract<Nat>:
    +spender : Nat <- Evm.caller()
    +allowed : Nat <- Evm.load2(2n, from, spender)
    spend : Nat <- spent(allowed, amount)
    left : Nat <- Evm.sub(allowed, spend)
    Evm.store2(2n, from, spender, left)
    move(from, to, amount)
    Evm.Contract.pure(Nat, 1n)

# Creates amount for to. The total supply must not overflow.
def mint(+to: Nat, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    supply : Nat <- Evm.sload(0n)
    total : Nat <- Evm.add(supply, amount)
    Evm.sstore(0n, total)
    credit(to, amount)
    Evm.log(transfer_event(), [0n, to], [amount])

# Destroys amount from the balance of from, which must cover it.
def burn(+from: Nat, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    b : Nat <- Evm.load(1n, from)
    rest : Nat <- Evm.sub(b, amount)
    Evm.store(1n, from, rest)
    supply : Nat <- Evm.sload(0n)
    total : Nat <- Evm.sub(supply, amount)
    Evm.sstore(0n, total)
    Evm.log(transfer_event(), [from, 0n], [amount])
