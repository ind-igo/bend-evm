import Base
import ../../src/Evm.bend as Evm
import ./program.bend as Token

# Each law gives every outcome from any state: any storage, caller, word
# limit and earlier logs, and any addresses. Slot 0 holds the total supply,
# the mapping at slot 1 holds balances, the mapping at slot 2 holds
# allowances, and slot 3 holds the owner. Storage is newest first, so new
# slots shadow old ones.

def supply(storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{0n})

def owner_of(storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{3n})

def balance(storage: List<&2, Evm.Slot>, who: Nat) -> Nat:
  Evm.lookup(storage, Evm.Mapped{Evm.Plain{1n}, who})

def allowed(storage: List<&2, Evm.Slot>, holder: Nat, spender: Nat) -> Nat:
  Evm.lookup(storage, Evm.Mapped{Evm.Mapped{Evm.Plain{2n}, holder}, spender})

# What transferFrom takes from the allowance: nothing when it is the
# largest word, limit - 1.
def spent(storage: List<&2, Evm.Slot>, holder: Nat, spender: Nat, limit: Nat, +amount: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_eq(allowed(storage, holder, spender), Nat.sub(limit, 1n)), 0n, amount)

def debit(+storage: List<&2, Evm.Slot>, +from: Nat, amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{1n}, from}, Nat.sub(balance(storage, from), amount)} <> storage

# The receiver's balance is read after the debit, so a transfer to oneself
# keeps the balance. Transfer writes no plain slot, so the supply stays.
law transfer:
  for +storage: List<&2, Evm.Slot>
  for +from: Nat
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for +to: Nat
  for +amount: Nat
  {Evm.run(Nat, Token.transfer(to, amount), Evm.State{storage, from, limit, logs})
    == Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(balance(storage, from), amount),
      Evm.Revert{},
      Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(Nat.add(balance(debit(storage, from, amount), to), amount), limit),
        Evm.Ok{1n, Evm.State{
          Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(balance(debit(storage, from, amount), to), amount)}
            <> debit(storage, from, amount), from, limit,
          Evm.Log{"Transfer(address,address,uint256)", [from, to], [amount]} <> logs}},
        Evm.Revert{})) : Evm.Outcome<Nat>}

# Only the owner can mint, and the supply and the balance must not overflow.
law mint:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for +to: Nat
  for +amount: Nat
  {Evm.run(Unit, Token.mint(to, amount), Evm.State{storage, who, limit, logs})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(who, owner_of(storage)),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(supply(storage), amount), limit),
        Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(balance(storage, to), amount), limit),
          Evm.Ok{Unit{}, Evm.State{
            Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(balance(storage, to), amount)}
              <> Evm.Slot{Evm.Plain{0n}, Nat.add(supply(storage), amount)} <> storage, who, limit,
            Evm.Log{"Transfer(address,address,uint256)", [0n, to], [amount]} <> logs}},
          Evm.Revert{}),
        Evm.Revert{}),
      Evm.Revert{}) : Evm.Outcome<Unit>}

law allowance:
  for +storage: List<&2, Evm.Slot>
  for who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for holder: Nat
  for spender: Nat
  {Evm.run(Nat, Token.allowance(holder, spender), Evm.State{storage, who, limit, logs})
    == Evm.Ok{allowed(storage, holder, spender), Evm.State{storage, who, limit, logs}} : Evm.Outcome<Nat>}

# Approve sets the allowance, whatever it was.
law approve:
  for storage: List<&2, Evm.Slot>
  for +who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for +spender: Nat
  for +amount: Nat
  {Evm.run(Nat, Token.approve(spender, amount), Evm.State{storage, who, limit, logs})
    == Evm.Ok{1n, Evm.State{Evm.Slot{Evm.Mapped{Evm.Mapped{Evm.Plain{2n}, who}, spender}, amount} <> storage, who, limit,
      Evm.Log{"Approval(address,address,uint256)", [who, spender], [amount]} <> logs}} : Evm.Outcome<Nat>}

# The caller spends from the allowance of `from`. The allowance must cover
# what is spent and the balance the amount; then the allowance goes down
# (unless it is unlimited) and the amount moves as in transfer.
law transferFrom:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for +from: Nat
  for +to: Nat
  for +amount: Nat
  {Evm.run(Nat, Token.transferFrom(from, to, amount), Evm.State{storage, who, limit, logs})
    == Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(allowed(storage, from, who), spent(storage, from, who, limit, amount)),
      Evm.Revert{},
      Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(balance(storage, from), amount),
        Evm.Revert{},
        Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(Nat.add(balance(debit(storage, from, amount), to), amount), limit),
          Evm.Ok{1n, Evm.State{
            Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(balance(debit(storage, from, amount), to), amount)}
              <> debit(Evm.Slot{Evm.Mapped{Evm.Mapped{Evm.Plain{2n}, from}, who}, Nat.sub(allowed(storage, from, who), spent(storage, from, who, limit, amount))}
                <> storage, from, amount), who, limit,
            Evm.Log{"Transfer(address,address,uint256)", [from, to], [amount]} <> logs}},
          Evm.Revert{}))) : Evm.Outcome<Nat>}

# The deployer becomes the owner and holds the initial supply.
law init:
  for storage: List<&2, Evm.Slot>
  for +who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for +supply: Nat
  {Evm.run(Unit, Token.init(supply), Evm.State{storage, who, limit, logs})
    == Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Mapped{Evm.Plain{1n}, who}, supply} <> Evm.Slot{Evm.Plain{0n}, supply}
      <> Evm.Slot{Evm.Plain{3n}, who} <> storage, who, limit,
      Evm.Log{"Transfer(address,address,uint256)", [0n, who], [supply]}
        <> Evm.Log{"OwnershipTransferred(address,address)", [0n, who], []} <> logs}} : Evm.Outcome<Unit>}

law owner:
  for +storage: List<&2, Evm.Slot>
  for who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  {Evm.run(Nat, Token.owner(), Evm.State{storage, who, limit, logs})
    == Evm.Ok{owner_of(storage), Evm.State{storage, who, limit, logs}} : Evm.Outcome<Nat>}

# Only the owner can hand ownership on.
law transferOwnership:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for +next: Nat
  {Evm.run(Unit, Token.transferOwnership(next), Evm.State{storage, who, limit, logs})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(who, owner_of(storage)),
      Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{3n}, next} <> storage, who, limit,
        Evm.Log{"OwnershipTransferred(address,address)", [owner_of(storage), next], []} <> logs}},
      Evm.Revert{}) : Evm.Outcome<Unit>}
