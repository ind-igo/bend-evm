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

# Supply across calls. A Call is one call to a function that can change
# storage; the view functions change nothing (see their laws). A call that
# reverts keeps the state.
type Call is Data:
  Transfer{who: Nat, to: Nat, amount: Nat}
  Mint{who: Nat, to: Nat, amount: Nat}
  Approve{who: Nat, spender: Nat, amount: Nat}
  TransferFrom{who: Nat, from: Nat, to: Nat, amount: Nat}
  TransferOwnership{who: Nat, next: Nat}

def after(-A: Data, o: Evm.Outcome<A>, s: Evm.State) -> Evm.State:
  match o:
    case Evm.Ok{_, t}:
      t
    case Evm.Revert{}:
      s

def as(+who: Nat, s: Evm.State) -> Evm.State:
  match s:
    case Evm.State{storage, _, limit, logs}:
      Evm.State{storage, who, limit, logs}

def step(c: Call, +s: Evm.State) -> Evm.State:
  match c:
    case Transfer{+who, +to, +amount}:
      after(Nat, Evm.run(Nat, Token.transfer(to, amount), as(who, s)), s)
    case Mint{+who, +to, +amount}:
      after(Unit, Evm.run(Unit, Token.mint(to, amount), as(who, s)), s)
    case Approve{+who, +spender, +amount}:
      after(Nat, Evm.run(Nat, Token.approve(spender, amount), as(who, s)), s)
    case TransferFrom{+who, +from, +to, +amount}:
      after(Nat, Evm.run(Nat, Token.transferFrom(from, to, amount), as(who, s)), s)
    case TransferOwnership{+who, +next}:
      after(Unit, Evm.run(Unit, Token.transferOwnership(next), as(who, s)), s)

def trace(calls: List<&2, Call>, +s: Evm.State) -> Evm.State:
  match calls:
    case Nil{}:
      s
    case +c <> rest:
      trace(rest, step(c, s))

# The state after `deployer` deploys the token with an initial supply.
def deployed(+deployer: Nat, +limit: Nat, +initial: Nat) -> Evm.State:
  after(Unit, Evm.run(Unit, Token.init(initial), Evm.State{[], deployer, limit, []}), Evm.State{[], deployer, limit, []})

# The balances of a list of accounts, summed.
def holdings(+storage: List<&2, Evm.Slot>, accounts: List<&2, Nat>) -> Nat:
  match accounts:
    case Nil{}:
      0n
    case +a <> rest:
      Nat.add(balance(storage, a), holdings(storage, rest))

def count(+who: Nat, accounts: List<&2, Nat>) -> Nat:
  match accounts:
    case Nil{}:
      0n
    case +a <> +rest:
      Bool.pick(Nat, Nat.is_eq(who, a), 1n+count(who, rest), count(who, rest))

def balanced(s: Evm.State, +accounts: List<&2, Nat>) -> Bool:
  match s:
    case Evm.State{+storage, _, _, _}:
      Nat.is_eq(supply(storage), holdings(storage, accounts))

# Each account whose balance the call can change is in the list once.
def listed(c: Call, +accounts: List<&2, Nat>) -> Bool:
  match c:
    case Transfer{+who, +to, _}:
      Bool.and(Nat.is_eq(1n, count(who, accounts)), Nat.is_eq(1n, count(to, accounts)))
    case Mint{_, +to, _}:
      Nat.is_eq(1n, count(to, accounts))
    case TransferFrom{_, +from, +to, _}:
      Bool.and(Nat.is_eq(1n, count(from, accounts)), Nat.is_eq(1n, count(to, accounts)))
    case _:
      True{}

def all_listed(calls: List<&2, Call>, +accounts: List<&2, Nat>) -> Bool:
  match calls:
    case Nil{}:
      True{}
    case +c <> rest:
      Bool.and(listed(c, accounts), all_listed(rest, accounts))

# From deployment, after any calls by anyone, the total supply is the sum of
# the balances of any list of accounts that has the deployer and every
# sender and receiver once. The list of every address below 2^160 is such a
# list (the dispatcher rejects larger addresses), so the total supply is the
# sum of all balances. The proof does not use the limit, so it holds at
# 2^256.
law supply_sum:
  for +calls: List<&2, Call>
  for +accounts: List<&2, Nat>
  for +deployer: Nat
  for +limit: Nat
  for +initial: Nat
  for +e: {True{} == Bool.and(Nat.is_eq(1n, count(deployer, accounts)), all_listed(calls, accounts)) : Bool}
  {True{} == balanced(trace(calls, deployed(deployer, limit, initial)), accounts) : Bool}
