import Base
import ../../src/Evm.bend as Evm
import ../../lib/ERC20.bend as ERC20

# A mintable ERC-20 on the ERC20 core, with EIP-2612 permit. The deployer
# owns it and receives the initial supply, the owner can mint more, as with
# OpenZeppelin's Ownable, and holders can burn.

# Storage after the ERC20 core: each owner's next permit nonce, and the owner.
def NONCES() -> Nat:
  3n

def OWNER() -> Nat:
  4n

def OwnershipTransferred(previous: Evm.Indexed(Evm.Address), next: Evm.Indexed(Evm.Address)) -> Evm.Event:
  Evm.Log{"OwnershipTransferred(address,address)", [previous, next], []}

def name() -> String:
  "Bend Token"

def symbol() -> String:
  "BEND"

def decimals() -> Evm.Contract(Evm.Uint8):
  Evm.Contract.pure(Nat, 18n)

def totalSupply() -> Evm.Contract(Nat):
  ERC20.totalSupply()

def balanceOf(who: Evm.Address) -> Evm.Contract(Nat):
  ERC20.balanceOf(who)

def allowance(holder: Evm.Address, spender: Evm.Address) -> Evm.Contract(Nat):
  ERC20.allowance(holder, spender)

def approve(+spender: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  ERC20.approve(spender, amount)

def transfer(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  ERC20.transfer(to, amount)

def transferFrom(+from: Evm.Address, +to: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  ERC20.transferFrom(from, to, amount)

# The constructor: the deployer is the owner and holds the initial supply.
def init(+supply: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    Evm.sstore(OWNER(), who)
    Evm.emit(OwnershipTransferred(0n, who))
    ERC20.mint(who, supply)

def owner() -> Evm.Contract(Evm.Address):
  Evm.sload(OWNER())

def transferOwnership(+next: Evm.Address) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    who : Nat <- Evm.caller()
    +boss : Nat <- Evm.sload(OWNER())
    Evm.require(Nat.is_eq(who, boss))
    Evm.sstore(OWNER(), next)
    Evm.emit(OwnershipTransferred(boss, next))

def mint(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    who : Nat <- Evm.caller()
    boss : Nat <- Evm.sload(OWNER())
    Evm.require(Nat.is_eq(who, boss))
    ERC20.mint(to, amount)

# A holder destroys some of its own tokens.
def burn(+amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    ERC20.burn(who, amount)

def nonces(who: Evm.Address) -> Evm.Contract(Nat):
  Evm.load(NONCES(), who)

# The EIP-712 domain separator: this token's name, version "1", this chain
# and this address.
def DOMAIN_SEPARATOR() -> Evm.Contract(Evm.Bytes32):
  do Evm.Contract<Nat>:
    +hash : Nat <- Evm.id(name())
    +kind : Nat <- Evm.id("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")
    +version : Nat <- Evm.id("1")
    +chain : Nat <- Evm.chainid()
    +me : Nat <- Evm.self()
    Evm.keccak([kind, hash, version, chain, me])

# EIP-2612: owner approves spender by a signature over the domain separator,
# instead of a transaction. The signature must be the owner's, before the
# deadline, and for the owner's next nonce, which it uses up.
def permit(+owner: Evm.Address, +spender: Evm.Address, +value: Nat, +deadline: Nat, +v: Evm.Uint8, +r: Evm.Bytes32,
  +s: Evm.Bytes32) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +separator : Nat <- DOMAIN_SEPARATOR()
    now : Nat <- Evm.timestamp()
    Evm.require(Bool.not(Nat.is_lt(deadline, now)))
    +nonce : Nat <- Evm.load(NONCES(), owner)
    next : Nat <- Evm.add(nonce, 1n)
    Evm.store(NONCES(), owner, next)
    +kind : Nat <- Evm.id("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)")
    +message : Nat <- Evm.keccak([kind, owner, spender, value, nonce, deadline])
    +digest : Nat <- Evm.typed(separator, message)
    +signer : Nat <- Evm.recover(digest, v, r, s)
    Evm.require(Bool.not(Nat.is_eq(signer, 0n)))
    Evm.require(Nat.is_eq(signer, owner))
    Evm.store2(ERC20.ALLOWANCES(), owner, spender, value)
    Evm.emit(ERC20.Approval(owner, spender, value))
