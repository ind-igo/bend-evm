import Base
import ../../src/Evm.bend as Evm
import ../erc20/ERC20.bend as ERC20

# Wrapped ether, after solmate's WETH. A deposit gives an equal amount of
# the token for the ether sent, and a withdrawal burns the token and sends
# the ether back. The token is the ERC20 core. There is no lock: a
# withdrawal burns before it pays, and LAWS.bend proves that the pay is its
# last step.

def Deposit(from: Evm.Indexed(Evm.Address), amount: Nat) -> Evm.Log:
  Evm.Log{"Deposit", [from], [amount]}

def Withdrawal(to: Evm.Indexed(Evm.Address), amount: Nat) -> Evm.Log:
  Evm.Log{"Withdrawal", [to], [amount]}

def name() -> String:
  "Wrapped Ether"

def symbol() -> String:
  "WETH"

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

def deposit() -> Evm.Payable(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    +amount : Nat <- Evm.callvalue()
    ERC20.mint(who, amount)
    Evm.emit(Deposit(who, amount))

def withdraw(+amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    ERC20.burn(who, amount)
    Evm.emit(Withdrawal(who, amount))
    Evm.pay(who, amount)

# Ether sent with no calldata is a deposit.
def receive() -> Evm.Payable(Unit):
  deposit()
