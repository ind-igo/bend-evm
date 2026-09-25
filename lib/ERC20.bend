import Base
import ../src/Evm.bend as Evm

# An ERC-20 base, after solmate's ERC20. A token imports it, defines name(),
# symbol() and decimals(), and exposes each standard function with a
# one-line def that calls this base; mint and burn are internal, like
# solmate's _mint and _burn. See examples/token.
#
# Storage: slot 0 holds the total supply, the mapping at slot 1 the balances,
# the mapping at slot 2, for each owner, the allowance of each spender, and
# the mapping at slot 3 each owner's next permit nonce. A token keeps its own
# state from slot 4 on.
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

# Moves amount and returns true, the end of transfer and transferFrom.
def pay(+from: Nat, +to: Nat, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  do Evm.Contract<Nat>:
    move(from, to, amount)
    Evm.Contract.pure(Nat, 1n)

# Lowers the allowance that from gave spender by amount, then pays.
def spend(+from: Nat, +to: Nat, +spender: Nat, +allowed: Nat, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  do Evm.Contract<Nat>:
    left : Nat <- Evm.sub(allowed, amount)
    Evm.store2(2n, from, spender, left)
    pay(from, to, amount)

# The caller spends from the allowance that `from` gave it. As in solmate,
# the largest allowance is unlimited, and transferFrom does not store it.
def transferFrom(+from: Evm.Address, +to: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  do Evm.Contract<Nat>:
    +spender : Nat <- Evm.caller()
    +allowed : Nat <- Evm.load2(2n, from, spender)
    top : Nat <- Evm.max()
    Evm.branch(Nat.is_eq(allowed, top), Nat, pay(from, to, amount), spend(from, to, spender, allowed, amount))

def nonces(who: Evm.Address) -> Evm.Contract(Nat):
  Evm.load(3n, who)

# The EIP-712 domain separator of a token whose name hashes to name, at
# version "1" on this chain and address.
def domain(+name: Nat) -> Evm.Contract(Evm.Bytes32):
  do Evm.Contract<Nat>:
    +kind : Nat <- Evm.id("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")
    +version : Nat <- Evm.id("1")
    +chain : Nat <- Evm.chainid()
    +me : Nat <- Evm.self()
    Evm.keccak([kind, name, version, chain, me])

# EIP-2612: owner approves spender by a signature over the domain separator,
# instead of a transaction. The signature must be the owner's, before the
# deadline, and for the owner's next nonce, which it uses up.
def permit(+separator: Nat, +owner: Evm.Address, +spender: Evm.Address, +value: Nat, +deadline: Nat, +v: Evm.Uint8,
  +r: Evm.Bytes32, +s: Evm.Bytes32) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    now : Nat <- Evm.timestamp()
    Evm.require(Bool.not(Nat.is_lt(deadline, now)))
    +nonce : Nat <- Evm.load(3n, owner)
    next : Nat <- Evm.add(nonce, 1n)
    Evm.store(3n, owner, next)
    +kind : Nat <- Evm.id("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)")
    +message : Nat <- Evm.keccak([kind, owner, spender, value, nonce, deadline])
    +digest : Nat <- Evm.typed(separator, message)
    +signer : Nat <- Evm.recover(digest, v, r, s)
    Evm.require(Bool.not(Nat.is_eq(signer, 0n)))
    Evm.require(Nat.is_eq(signer, owner))
    Evm.store2(2n, owner, spender, value)
    Evm.log(approval_event(), [owner, spender], [value])

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
