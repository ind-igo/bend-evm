import Base
import ../../../src/Evm.bend as Evm

# Bytes and strings, for tests/bytes.test.js: parameters that the contract
# passes on in a log, an error, a call and a tuple result, their length,
# and their hash.

def Note(id: Evm.Indexed(Nat), text: Evm.Str, data: Evm.Bytes) -> Evm.Log:
  Evm.Log{"Note", [id], Evm.abi([Evm.Dynamic{text}, Evm.Dynamic{data}])}

def Refused(code: Nat, reason: Evm.Str) -> Evm.Error:
  Evm.Error{"Refused", Evm.abi([Evm.Word{code}, Evm.Dynamic{reason}])}

def Echo(data: Evm.Bytes, size: Nat) -> Evm.Values:
  Evm.Values{Evm.abi([Evm.Dynamic{data}, Evm.Word{size}])}

def onData(target: Evm.Address, sender: Evm.Address, data: Evm.Bytes) -> Evm.Call:
  Evm.Call{target, "onData", Evm.abi([Evm.Word{sender}, Evm.Dynamic{data}])}

def note(+id: Nat, +text: Evm.Str, +data: Evm.Bytes) -> Evm.Contract(Unit):
  Evm.emit(Note(id, text, data))

def echo(+data: Evm.Bytes) -> Evm.Contract(Evm.Values):
  Evm.Contract.pure(Evm.Values, Echo(data, Evm.length(data)))

def size(data: Evm.Bytes) -> Evm.Contract(Nat):
  Evm.Contract.pure(Nat, Evm.length(data))

def refuse(+code: Nat, +reason: Evm.Str) -> Evm.Contract(Unit):
  Evm.ensure(Nat.is_eq(code, 0n), Refused(code, reason))

def hash(data: Evm.Bytes) -> Evm.Contract(Nat):
  Evm.keccak.bytes(data)

# Calls target's onData with the caller and data, and returns its word.
def forward(+target: Evm.Address, +data: Evm.Bytes) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +who : Nat <- Evm.caller()
    Evm.call(onData(target, who, data))
