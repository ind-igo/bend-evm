import Base
import ../../../src/Evm.bend as Evm
import ../../../examples/amm/Math.bend as Math

# One entry for each word operation, for checked mul, div and mod, and for
# the AMM's square root, for tests/math.test.js.

def add(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.unchecked.add(a, b)

def sub(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.unchecked.sub(a, b)

def mul(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.unchecked.mul(a, b)

def div(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.unchecked.div(a, b)

def sdiv(a: Evm.Int, b: Evm.Int) -> Evm.Contract(Evm.Int):
  Evm.sdiv(a, b)

def mod(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.unchecked.mod(a, b)

def smod(a: Evm.Int, b: Evm.Int) -> Evm.Contract(Evm.Int):
  Evm.smod(a, b)

def addmod(a: Nat, b: Nat, c: Nat) -> Evm.Contract(Nat):
  Evm.addmod(a, b, c)

def mulmod(a: Nat, b: Nat, c: Nat) -> Evm.Contract(Nat):
  Evm.mulmod(a, b, c)

def exp(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.unchecked.exp(a, b)

def signextend(a: Nat, b: Nat) -> Evm.Contract(Evm.Int):
  Evm.signextend(a, b)

def lt(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.lt(a, b)

def gt(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.gt(a, b)

def slt(a: Evm.Int, b: Evm.Int) -> Evm.Contract(Nat):
  Evm.slt(a, b)

def sgt(a: Evm.Int, b: Evm.Int) -> Evm.Contract(Nat):
  Evm.sgt(a, b)

def eq(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.eq(a, b)

def iszero(a: Nat) -> Evm.Contract(Nat):
  Evm.iszero(a)

def and(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.and(a, b)

def or(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.or(a, b)

def xor(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.xor(a, b)

def not(a: Nat) -> Evm.Contract(Nat):
  Evm.not(a)

def byte(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.byte(a, b)

def shl(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.shl(a, b)

def shr(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.shr(a, b)

def sar(a: Nat, b: Evm.Int) -> Evm.Contract(Evm.Int):
  Evm.sar(a, b)

def checked_mul(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.mul(a, b)

def checked_div(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.div(a, b)

def checked_mod(a: Nat, b: Nat) -> Evm.Contract(Nat):
  Evm.mod(a, b)

def sqrt(a: Nat) -> Evm.Contract(Nat):
  Math.sqrt(a)
