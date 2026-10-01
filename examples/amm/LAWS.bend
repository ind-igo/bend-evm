import Base
import ../../src/Evm.bend as Evm
import ../../src/calls.bend as Calls
import ../erc20/ERC20.bend as ERC20
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
# two tokens and a flash swap's receiver give, and for every callback that
# they make into the pair while it pays, at any depth, from any state that
# the callbacks leave: it does not need the lock. The swap reads the
# reserves before it pays, checks the balances after it against them, and
# then writes those balances as the reserves, so what the callbacks did in
# between cannot pass the check.
law swap:
  for +steps: List<&2, Calls.Step>
  for +s: Evm.State
  for +amount0Out: Nat
  for +amount1Out: Nat
  for +to: Nat
  for +data: Evm.Bytes
  {True{} == kept(product(s), Calls.run(Cert.entry.table(), Unit, Pair.swap(amount0Out, amount1Out, to, data), steps, s)) : Bool}

def lock(+storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Transient{Pair.LOCK()})

# While one of swap, mint, burn and sync runs, it holds the lock, and each
# of them raises Locked(). So a callback cannot sync and mint against the
# reserves of a swap that paid out and did not check yet. The ERC20
# functions and the views have no lock.
law swap_locked:
  for +storage: List<&2, Evm.Slot>
  for +caller: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +amount0Out: Nat
  for +amount1Out: Nat
  for +to: Nat
  for +data: Evm.Bytes
  for +h: {False{} == Nat.is_eq(lock(storage), 0n) : Bool}
  {Evm.run(Unit, Pair.swap(amount0Out, amount1Out, to, data), Evm.State{storage, caller, limit, logs, world})
    == Evm.Raise{Pair.Locked()} : Evm.Outcome<Unit>}

law mint_locked:
  for +storage: List<&2, Evm.Slot>
  for +caller: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +to: Nat
  for +h: {False{} == Nat.is_eq(lock(storage), 0n) : Bool}
  {Evm.run(Nat, Pair.mint(to), Evm.State{storage, caller, limit, logs, world}) == Evm.Raise{Pair.Locked()} : Evm.Outcome<Nat>}

law burn_locked:
  for +storage: List<&2, Evm.Slot>
  for +caller: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +to: Nat
  for +h: {False{} == Nat.is_eq(lock(storage), 0n) : Bool}
  {Evm.run(Unit, Pair.burn(to), Evm.State{storage, caller, limit, logs, world}) == Evm.Raise{Pair.Locked()} : Evm.Outcome<Unit>}

law sync_locked:
  for +storage: List<&2, Evm.Slot>
  for +caller: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +h: {False{} == Nat.is_eq(lock(storage), 0n) : Bool}
  {Evm.run(Unit, Pair.sync(), Evm.State{storage, caller, limit, logs, world}) == Evm.Raise{Pair.Locked()} : Evm.Outcome<Unit>}

def supply(+storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{ERC20.SUPPLY()})

def token0(+storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{Pair.TOKEN0()})

def token1(+storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{Pair.TOKEN1()})

# sync makes the balances that the tokens report the reserves. It takes the
# lock first, and gives it back at the end.
law sync:
  for +storage: List<&2, Evm.Slot>
  for +caller: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +facts: List<&2, Evm.Fact>
  for +readings: List<&2, Nat>
  for +self: Nat
  for +hashes: List<&2, Evm.Hashed>
  for +signers: List<&2, Evm.Signed>
  for +q0: Evm.Call
  for +b0: Nat
  for +q1: Evm.Call
  for +b1: Nat
  for +more: List<&2, Evm.Answer>
  {Evm.run(Unit, Pair.sync(), Evm.State{storage, caller, limit, logs,
      Evm.World{facts, readings, self, hashes, signers, Evm.Answer{q0, b0} <> Evm.Answer{q1, b1} <> more}})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(lock(storage), 0n),
      Bool.pick(Evm.Outcome<Unit>, Evm.same.call(q0, Evm.Call{token0(storage), "balanceOf", [self]}),
        Bool.pick(Evm.Outcome<Unit>, Evm.same.call(q1, Evm.Call{token1(storage), "balanceOf", [self]}),
          Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Transient{Pair.LOCK()}, 0n} <> Evm.Slot{Evm.Plain{Pair.RESERVE1()}, b1}
            <> Evm.Slot{Evm.Plain{Pair.RESERVE0()}, b0} <> Evm.Slot{Evm.Transient{Pair.LOCK()}, 1n} <> storage,
            caller, limit, Pair.Sync(b0, b1) <> logs, Evm.World{facts, readings, self, hashes, signers, more}}},
          Evm.Revert{}),
        Evm.Revert{}),
      Evm.Raise{Pair.Locked()}) : Evm.Outcome<Unit>}

# For each token, the reserve for each liquidity token does not go down
# from storage st to storage t: supply(t) * reserve(st) <= supply(st) *
# reserve(t).
def gained(+st: List<&2, Evm.Slot>, +t: List<&2, Evm.Slot>) -> Bool:
  Bool.and(Bool.not(Nat.is_lt(Nat.mul(supply(st), reserve0(t)), Nat.mul(supply(t), reserve0(st)))),
    Bool.not(Nat.is_lt(Nat.mul(supply(st), reserve1(t)), Nat.mul(supply(t), reserve1(st)))))

# A mint into a pair that has liquidity ends with gained, or does not end
# well. The first mint sets the price, so it has no bound here.
def fair(+st: List<&2, Evm.Slot>, o: Evm.Outcome<Nat>) -> Bool:
  match o:
    case Evm.Ok{_, t}:
      match t:
        case Evm.State{+storage, _, _, _, _}:
          Bool.or(Nat.is_eq(supply(st), 0n), gained(st, storage))
    case Evm.Revert{}:
      True{}
    case Evm.Raise{_}:
      True{}
    case Evm.Calling{_, _, _}:
      True{}

# A mint does not dilute the liquidity tokens: the new ones buy no more of
# each reserve than the tokens that the minter sent. The rounding goes to
# the pair.
law mint:
  for +storage: List<&2, Evm.Slot>
  for +caller: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +to: Nat
  {True{} == fair(storage, Evm.run(Nat, Pair.mint(to), Evm.State{storage, caller, limit, logs, world})) : Bool}

# The first two words of a log's data are at most the burned share of each
# balance: a * s <= l * b, for liquidity l of supply s.
def within(+l: Nat, +s: Nat, +b0: Nat, +b1: Nat, data: List<&2, Nat>) -> Bool:
  match data:
    case a0 <> a1 <> _:
      Bool.and(Bool.not(Nat.is_lt(Nat.mul(l, b0), Nat.mul(a0, s))), Bool.not(Nat.is_lt(Nat.mul(l, b1), Nat.mul(a1, s))))
    case _:
      True{}

# A burn that ends well logs Burn last, with the amounts that it paid.
def paid(+l: Nat, +s: Nat, +b0: Nat, +b1: Nat, o: Evm.Outcome<Unit>) -> Bool:
  match o:
    case Evm.Ok{_, t}:
      match t:
        case Evm.State{_, _, _, logs, _}:
          match logs:
            case Evm.Log{_, _, data} <> _:
              within(l, s, b0, b1, data)
            case Nil{}:
              True{}
    case Evm.Revert{}:
      True{}
    case Evm.Raise{_}:
      True{}
    case Evm.Calling{_, _, _}:
      True{}

# A burn pays each token no more than the burned share of the pair's
# balance, b0 and b1 here: amount * supply <= liquidity * balance. The
# rounding goes to the pair. This holds whatever the tokens answer and
# whatever their callbacks do while the pair pays.
law burn:
  for +steps: List<&2, Calls.Step>
  for +storage: List<&2, Evm.Slot>
  for +caller: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +facts: List<&2, Evm.Fact>
  for +readings: List<&2, Nat>
  for +self: Nat
  for +hashes: List<&2, Evm.Hashed>
  for +signers: List<&2, Evm.Signed>
  for +q0: Evm.Call
  for +b0: Nat
  for +q1: Evm.Call
  for +b1: Nat
  for +more: List<&2, Evm.Answer>
  for +to: Nat
  {True{} == paid(Evm.lookup(storage, Evm.Mapped{Evm.Plain{ERC20.BALANCES()}, self}), supply(storage), b0, b1,
    Calls.run(Cert.entry.table(), Unit, Pair.burn(to), steps, Evm.State{storage, caller, limit, logs,
      Evm.World{facts, readings, self, hashes, signers, Evm.Answer{q0, b0} <> Evm.Answer{q1, b1} <> more}})) : Bool}
