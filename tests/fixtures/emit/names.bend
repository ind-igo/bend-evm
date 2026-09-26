import Base
import ../../../src/Evm.bend as Evm
import ./program.bend as Other

# Its own TooSmall has the signature of Other.TooSmall, with other parameter
# names. The IR does not say which def an error came from, so the ABI names
# neither.
def TooSmall(have: Nat, need: Nat) -> Evm.Error:
  Evm.Error{"TooSmall(uint256,uint256)", [have, need]}

def check(+x: Nat) -> Evm.Contract(Unit):
  Evm.ensure(Nat.is_lt(5n, x), TooSmall(x, 6n))
