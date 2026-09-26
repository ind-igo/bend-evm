import Base
import ../src/Evm.bend as Evm

# The ERC-20 core, after solmate's ERC20. A token imports it, defines name(),
# symbol() and decimals(), and exposes each function with a one-line def;
# mint and burn are internal, like solmate's _mint and _burn. See
# examples/token.
#
# As in solmate, there are no zero-address checks, and the largest allowance
# is unlimited. Unlike solmate, the receiver's add is checked. It cannot fail,
# because no balance exceeds the total supply, but it costs a little gas.

# Storage. A token keeps its own state from slot 3 on.
def SUPPLY() -> Nat:
  0n

def BALANCES() -> Nat:
  1n

# For each owner, the allowance of each spender.
def ALLOWANCES() -> Nat:
  2n

# Events. The reader makes each log from the name and the parameter types,
# and the certificate proves that the body gives the same log.
def Transfer(from: Evm.Indexed(Evm.Address), to: Evm.Indexed(Evm.Address), amount: Nat) -> Evm.Event:
  Evm.Log{"Transfer", [from, to], [amount]}

def Approval(owner: Evm.Indexed(Evm.Address), spender: Evm.Indexed(Evm.Address), amount: Nat) -> Evm.Event:
  Evm.Log{"Approval", [owner, spender], [amount]}

def totalSupply() -> Evm.Contract(Nat):
  Evm.sload(SUPPLY())

def balanceOf(who: Evm.Address) -> Evm.Contract(Nat):
  Evm.load(BALANCES(), who)

def allowance(owner: Evm.Address, spender: Evm.Address) -> Evm.Contract(Nat):
  Evm.load2(ALLOWANCES(), owner, spender)

def approve(+spender: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  do Evm.Contract<Nat>:
    +owner : Nat <- Evm.caller()
    Evm.store2(ALLOWANCES(), owner, spender, amount)
    Evm.emit(Approval(owner, spender, amount))
    Evm.Contract.pure(Nat, 1n)

# Moves amount from one balance to another and returns true.
def move(+from: Nat, +to: Nat, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  do Evm.Contract<Nat>:
    a : Nat <- Evm.load(BALANCES(), from)
    left : Nat <- Evm.sub(a, amount)
    Evm.store(BALANCES(), from, left)
    b : Nat <- Evm.load(BALANCES(), to)
    sum : Nat <- Evm.add(b, amount)
    Evm.store(BALANCES(), to, sum)
    Evm.emit(Transfer(from, to, amount))
    Evm.Contract.pure(Nat, 1n)

def transfer(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  do Evm.Contract<Nat>:
    +from : Nat <- Evm.caller()
    move(from, to, amount)

# The caller spends from the allowance that from gave it. The largest
# allowance is unlimited and is not stored again.
def transferFrom(+from: Evm.Address, +to: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  do Evm.Contract<Nat>:
    +spender : Nat <- Evm.caller()
    +allowed : Nat <- Evm.load2(ALLOWANCES(), from, spender)
    top : Nat <- Evm.max()
    Evm.branch(Nat, Nat.is_eq(allowed, top), move(from, to, amount),
      do Evm.Contract<Nat>:
        left : Nat <- Evm.sub(allowed, amount)
        Evm.store2(ALLOWANCES(), from, spender, left)
        move(from, to, amount))

# Creates amount for to. The total supply must not overflow.
def mint(+to: Nat, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    supply : Nat <- Evm.sload(SUPPLY())
    total : Nat <- Evm.add(supply, amount)
    Evm.sstore(SUPPLY(), total)
    b : Nat <- Evm.load(BALANCES(), to)
    sum : Nat <- Evm.add(b, amount)
    Evm.store(BALANCES(), to, sum)
    Evm.emit(Transfer(0n, to, amount))

# Destroys amount from the balance of from, which must cover it.
def burn(+from: Nat, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    b : Nat <- Evm.load(BALANCES(), from)
    left : Nat <- Evm.sub(b, amount)
    Evm.store(BALANCES(), from, left)
    supply : Nat <- Evm.sload(SUPPLY())
    total : Nat <- Evm.sub(supply, amount)
    Evm.sstore(SUPPLY(), total)
    Evm.emit(Transfer(from, 0n, amount))
