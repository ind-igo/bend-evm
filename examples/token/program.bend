import Base
import ../../src/Evm.bend as Evm
import ../../lib/ERC20.bend as ERC20

# A mintable ERC-20 on the ERC20 base. The deployer owns it and receives the
# initial supply, the owner can mint more, as with OpenZeppelin's Ownable,
# and holders can burn. Slot 4 holds the owner.

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

def nonces(who: Evm.Address) -> Evm.Contract(Nat):
  ERC20.nonces(who)

def DOMAIN_SEPARATOR() -> Evm.Contract(Evm.Bytes32):
  do Evm.Contract<Nat>:
    +hash : Nat <- Evm.id(name())
    ERC20.domain(hash)

def permit(+owner: Evm.Address, +spender: Evm.Address, +value: Nat, +deadline: Nat, +v: Evm.Uint8, +r: Evm.Bytes32,
  +s: Evm.Bytes32) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +separator : Nat <- DOMAIN_SEPARATOR()
    ERC20.permit(separator, owner, spender, value, deadline, v, r, s)

def ownership_event() -> String:
  "OwnershipTransferred(address,address)"

# The constructor: the deployer is the owner and holds the initial supply.
def init(+supply: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    Evm.sstore(4n, who)
    Evm.log(ownership_event(), [0n, who], [])
    ERC20.mint(who, supply)

def owner() -> Evm.Contract(Evm.Address):
  Evm.sload(4n)

def transferOwnership(+next: Evm.Address) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    who : Nat <- Evm.caller()
    +boss : Nat <- Evm.sload(4n)
    Evm.require(Nat.is_eq(who, boss))
    Evm.sstore(4n, next)
    Evm.log(ownership_event(), [boss, next], [])

# A holder destroys some of its own tokens.
def burn(+amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    ERC20.burn(who, amount)

def mint(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    who : Nat <- Evm.caller()
    boss : Nat <- Evm.sload(4n)
    Evm.require(Nat.is_eq(who, boss))
    ERC20.mint(to, amount)
