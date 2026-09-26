import Base
import ../../../src/Evm.bend as Evm
import ./IERC20.bend as IERC20

# A contract that reads other ERC-20s with Evm.view. It is a small token too,
# so a test can point it at itself.

# Sets who's balance and adds it to the supply.
def mint(+who: Evm.Address, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +supply : Nat <- Evm.sload(1n)
    +more : Nat <- Evm.add(supply, amount)
    Evm.store(0n, who, amount)
    Evm.sstore(1n, more)

def balanceOf(who: Evm.Address) -> Evm.Contract(Nat):
  Evm.load(0n, who)

def totalSupply() -> Evm.Contract(Nat):
  Evm.sload(1n)

# The balance that token gives for who. who is any word, so that a test can
# make the token revert.
def holding(token: Evm.Address, who: Nat) -> Evm.Contract(Nat):
  Evm.view(IERC20.balanceOf(token, who))

# The supply that the others hold: two calls, in order, then a checked sub.
def others(+token: Evm.Address, who: Evm.Address) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +held : Nat <- Evm.view(IERC20.balanceOf(token, who))
    +supply : Nat <- Evm.view(IERC20.totalSupply(token))
    Evm.sub(supply, held)
