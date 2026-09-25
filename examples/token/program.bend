import Base
import ../../src/Evm.bend as Evm
import ../../lib/ERC20.bend as ERC20

# A mintable ERC-20 on the ERC20 base. The deployer owns it and receives the
# initial supply, and the owner can mint more, as with OpenZeppelin's
# Ownable. Slot 3 holds the owner.

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

def ownership_event() -> String:
  "OwnershipTransferred(address,address)"

# The constructor: the deployer is the owner and holds the initial supply.
def init(+supply: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    Evm.sstore(3n, who)
    Evm.log(ownership_event(), [0n, who], [])
    ERC20.mint(who, supply)

def owner() -> Evm.Contract(Evm.Address):
  Evm.sload(3n)

def transferOwnership(+next: Evm.Address) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    who : Nat <- Evm.caller()
    +boss : Nat <- Evm.sload(3n)
    Evm.require(Nat.is_eq(who, boss))
    Evm.sstore(3n, next)
    Evm.log(ownership_event(), [boss, next], [])

def mint(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    who : Nat <- Evm.caller()
    boss : Nat <- Evm.sload(3n)
    Evm.require(Nat.is_eq(who, boss))
    ERC20.mint(to, amount)
