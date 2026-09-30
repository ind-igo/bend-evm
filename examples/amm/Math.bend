import Base
import ../../src/Evm.bend as Evm

# The floor of the square root of x, after solady's FixedPointMathLib.sqrt:
# an estimate from the highest bits of x (x > 2^136 - 1 is shr(136, x) > 0), seven Newton steps, and a last
# step down when the steps end one above the root. It has no loop, so it
# compiles to straight code. tests/math.test.js checks it on anvil.
def newton(+x: Nat, +z: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +q : Nat <- Evm.unchecked.div(x, z)
    +sum : Nat <- Evm.unchecked.add(z, q)
    Evm.shr(1n, sum)

def sqrt(+x: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +h7 : Nat <- Evm.shr(136n, x)
    +c7 : Nat <- Evm.lt(0n, h7)
    +r7 : Nat <- Evm.shl(7n, c7)
    +x6 : Nat <- Evm.shr(r7, x)
    +h6 : Nat <- Evm.shr(72n, x6)
    +c6 : Nat <- Evm.lt(0n, h6)
    +s6 : Nat <- Evm.shl(6n, c6)
    +r6 : Nat <- Evm.or(r7, s6)
    +x5 : Nat <- Evm.shr(r6, x)
    +h5 : Nat <- Evm.shr(40n, x5)
    +c5 : Nat <- Evm.lt(0n, h5)
    +s5 : Nat <- Evm.shl(5n, c5)
    +r5 : Nat <- Evm.or(r6, s5)
    +x4 : Nat <- Evm.shr(r5, x)
    +h4 : Nat <- Evm.shr(24n, x4)
    +c4 : Nat <- Evm.lt(0n, h4)
    +s4 : Nat <- Evm.shl(4n, c4)
    +r : Nat <- Evm.or(r5, s4)
    +half : Nat <- Evm.shr(1n, r)
    +z0 : Nat <- Evm.shl(half, 181n)
    +top : Nat <- Evm.shr(r, x)
    +y : Nat <- Evm.unchecked.add(top, 65536n)
    +m : Nat <- Evm.unchecked.mul(z0, y)
    +z1 : Nat <- Evm.shr(18n, m)
    +z2 : Nat <- newton(x, z1)
    +z3 : Nat <- newton(x, z2)
    +z4 : Nat <- newton(x, z3)
    +z5 : Nat <- newton(x, z4)
    +z6 : Nat <- newton(x, z5)
    +z7 : Nat <- newton(x, z6)
    +z8 : Nat <- newton(x, z7)
    +q : Nat <- Evm.unchecked.div(x, z8)
    +over : Nat <- Evm.lt(q, z8)
    Evm.unchecked.sub(z8, over)

# One Newton step: (z + x / z) / 2. The EVM's div gives 0 when z is 0.