import Base
import ../../src/Evm.bend as Evm
import ../../src/calls.bend as Calls
import ./Pair.bend as Pair
import ./CERT.bend as Cert

def reserve0(+storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{Pair.RESERVE0()})

def reserve1(+storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{Pair.RESERVE1()})

# x·y: the product of the reserves.
def product(s: Evm.State) -> Nat:
  match s:
    case Evm.State{+storage, _, _, _, _}:
      Nat.mul(reserve0(storage), reserve1(storage))

# The outcome ends with the product at least k, or does not end well.
def kept(+k: Nat, o: Evm.Outcome<Unit>) -> Bool:
  match o:
    case Evm.Ok{_, t}:
      Bool.not(Nat.is_lt(product(t), k))
    case Evm.Revert{}:
      True{}
    case Evm.Raise{_}:
      True{}
    case Evm.Calling{_, _, _}:
      True{}

# A swap does not make x·y go down. This holds for every answer that the
# two tokens give and for every callback that they make into the pair while
# it pays, at any depth: other swaps, mints, burns and syncs. There is no
# lock. The swap reads the reserves before it pays, checks the balances
# after it against them, and then writes those balances as the reserves, so
# what the callbacks did in between cannot pass the check.
law swap:
  for +steps: List<&2, Calls.Step>
  for +s: Evm.State
  for +amount0Out: Nat
  for +amount1Out: Nat
  for +to: Nat
  {True{} == kept(product(s), Calls.run(Cert.entry.table(), Unit, Pair.swap(amount0Out, amount1Out, to), steps, s)) : Bool}
