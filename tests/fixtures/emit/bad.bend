import Base
import ../../../src/Evm.bend as Evm

# Events and errors that the reader must reject.

def Late(amount: Nat, from: Evm.Indexed(Evm.Address)) -> Evm.Event:
  Evm.Log{"Late", [from], [amount]}

def Wide(a: Evm.Indexed(Nat), b: Evm.Indexed(Nat), c: Evm.Indexed(Nat), d: Evm.Indexed(Nat)) -> Evm.Event:
  Evm.Log{"Wide", [a, b, c, d], []}

# An indexed field after a data field.
def late() -> Evm.Contract(Unit):
  Evm.emit(Late(1n, 2n))

# Four indexed fields.
def wide() -> Evm.Contract(Unit):
  Evm.emit(Wide(1n, 2n, 3n, 4n))

# A def that returns a log but is not marked as an event.
def Plain(x: Nat) -> Evm.Log:
  Evm.Log{"Plain", [], [x]}

def plain() -> Evm.Contract(Unit):
  Evm.emit(Plain(1n))

# Two events with one signature but different indexed parameters.
def Moved(from: Evm.Indexed(Evm.Address), amount: Nat) -> Evm.Event:
  Evm.Log{"Moved", [from], [amount]}

def other.Moved(from: Evm.Address, amount: Nat) -> Evm.Event:
  Evm.Log{"Moved", [], [from, amount]}

def one() -> Evm.Contract(Unit):
  Evm.emit(Moved(1n, 2n))

def two() -> Evm.Contract(Unit):
  Evm.emit(other.Moved(1n, 2n))

# A log without an event def.
def raw() -> Evm.Contract(Unit):
  Evm.emit(Evm.Log{"E", [], [0n]})

# Contracts emit events. They do not call Evm.log.
def logged() -> Evm.Contract(Unit):
  Evm.log("E", [], [0n])

# With "(uint256)", its signature has 137 bytes, which one Keccak block
# cannot hold.
def AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA(x: Nat) -> Evm.Event:
  Evm.Log{"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA", [], [x]}

def long() -> Evm.Contract(Unit):
  Evm.emit(AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA(1n))

# An error field cannot be a topic.
def Marked(x: Evm.Indexed(Nat)) -> Evm.Error:
  Evm.Error{"Marked", [x]}

def marked() -> Evm.Contract(Unit):
  Evm.ensure(Nat.is_eq(1n, 1n), Marked(1n))

# An error without an error def.
def bare() -> Evm.Contract(Unit):
  Evm.ensure(Nat.is_eq(1n, 1n), Evm.Error{"E", []})

# Solidity's own panic error.
def Panic(code: Nat) -> Evm.Error:
  Evm.Error{"Panic", [code]}

def panics() -> Evm.Contract(Unit):
  Evm.ensure(Nat.is_eq(1n, 1n), Panic(1n))

# Two errors with one name but other parameter types, which the model
# cannot tell apart.
def Short(amount: Nat) -> Evm.Error:
  Evm.Error{"Short", [amount]}

def other.Short(who: Evm.Address) -> Evm.Error:
  Evm.Error{"Short", [who]}

def short() -> Evm.Contract(Unit):
  Evm.ensure(Nat.is_eq(1n, 1n), Short(1n))

# The same for two events.
def Twice(x: Nat) -> Evm.Event:
  Evm.Log{"Twice", [], [x]}

def other.Twice(x: Evm.Address) -> Evm.Event:
  Evm.Log{"Twice", [], [x]}

def twice() -> Evm.Contract(Unit):
  Evm.emit(Twice(1n))
