import Base
import ../../src/Evm.bend as Evm
import ./program.bend as Token

# Each law gives every outcome from any state: any storage, caller, word
# limit and earlier logs, and any addresses. Slot 0 holds the total supply,
# the mapping at slot 1 holds balances, the mapping at slot 2 holds
# allowances, the mapping at slot 3 holds nonces, and slot 4 holds the owner. Storage is newest first, so new
# slots shadow old ones.

def supply(storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{0n})

def owner_of(storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{4n})

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
  for world: Evm.World
  for +to: Nat
  for +amount: Nat
  {Evm.run(Nat, Token.transfer(to, amount), Evm.State{storage, from, limit, logs, world})
    == Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(balance(storage, from), amount),
      Evm.Revert{},
      Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(Nat.add(balance(debit(storage, from, amount), to), amount), limit),
        Evm.Ok{1n, Evm.State{Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(balance(debit(storage, from, amount), to), amount)}
            <> debit(storage, from, amount), from, limit, Evm.Log{"Transfer(address,address,uint256)", [from, to], [amount]} <> logs, world}},
        Evm.Revert{})) : Evm.Outcome<Nat>}

# Only the owner can mint, and the supply and the balance must not overflow.
law mint:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for +to: Nat
  for +amount: Nat
  {Evm.run(Unit, Token.mint(to, amount), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(who, owner_of(storage)),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(supply(storage), amount), limit),
        Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(balance(storage, to), amount), limit),
          Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(balance(storage, to), amount)}
              <> Evm.Slot{Evm.Plain{0n}, Nat.add(supply(storage), amount)} <> storage, who, limit, Evm.Log{"Transfer(address,address,uint256)", [0n, to], [amount]} <> logs, world}},
          Evm.Revert{}),
        Evm.Revert{}),
      Evm.Revert{}) : Evm.Outcome<Unit>}

# A burn lowers the caller's balance and the supply; it reverts unless both
# cover the amount.
law burn:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for +amount: Nat
  {Evm.run(Unit, Token.burn(amount), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(balance(storage, who), amount),
      Evm.Revert{},
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(supply(storage), amount),
        Evm.Revert{},
        Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{0n}, Nat.sub(supply(storage), amount)} <> debit(storage, who, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [who, 0n], [amount]} <> logs, world}})) : Evm.Outcome<Unit>}

law allowance:
  for +storage: List<&2, Evm.Slot>
  for who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for holder: Nat
  for spender: Nat
  {Evm.run(Nat, Token.allowance(holder, spender), Evm.State{storage, who, limit, logs, world})
    == Evm.Ok{allowed(storage, holder, spender), Evm.State{storage, who, limit, logs, world}} : Evm.Outcome<Nat>}

# Approve sets the allowance, whatever it was.
law approve:
  for storage: List<&2, Evm.Slot>
  for +who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for +spender: Nat
  for +amount: Nat
  {Evm.run(Nat, Token.approve(spender, amount), Evm.State{storage, who, limit, logs, world})
    == Evm.Ok{1n, Evm.State{Evm.Slot{Evm.Mapped{Evm.Mapped{Evm.Plain{2n}, who}, spender}, amount} <> storage, who, limit, Evm.Log{"Approval(address,address,uint256)", [who, spender], [amount]} <> logs, world}} : Evm.Outcome<Nat>}

# The caller spends from the allowance of `from`. The allowance must cover
# what is spent and the balance the amount; then the allowance goes down
# (unless it is unlimited) and the amount moves as in transfer.
law transferFrom:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for +from: Nat
  for +to: Nat
  for +amount: Nat
  {Evm.run(Nat, Token.transferFrom(from, to, amount), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(allowed(storage, from, who), spent(storage, from, who, limit, amount)),
      Evm.Revert{},
      Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(balance(storage, from), amount),
        Evm.Revert{},
        Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(Nat.add(balance(debit(storage, from, amount), to), amount), limit),
          Evm.Ok{1n, Evm.State{Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(balance(debit(storage, from, amount), to), amount)}
              <> debit(Evm.Slot{Evm.Mapped{Evm.Mapped{Evm.Plain{2n}, from}, who}, Nat.sub(allowed(storage, from, who), spent(storage, from, who, limit, amount))}
                <> storage, from, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [from, to], [amount]} <> logs, world}},
          Evm.Revert{}))) : Evm.Outcome<Nat>}

# The deployer becomes the owner and receives the initial supply by a mint,
# which reverts only on overflow. At deployment the storage is empty, so
# that needs an initial supply of at least the limit.
law init:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for +initial: Nat
  {Evm.run(Unit, Token.init(initial), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(supply(storage), initial), limit),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(balance(storage, who), initial), limit),
        Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Mapped{Evm.Plain{1n}, who}, Nat.add(balance(storage, who), initial)}
          <> Evm.Slot{Evm.Plain{0n}, Nat.add(supply(storage), initial)} <> Evm.Slot{Evm.Plain{4n}, who} <> storage, who, limit, Evm.Log{"Transfer(address,address,uint256)", [0n, who], [initial]}
            <> Evm.Log{"OwnershipTransferred(address,address)", [0n, who], []} <> logs, world}},
        Evm.Revert{}),
      Evm.Revert{}) : Evm.Outcome<Unit>}

law owner:
  for +storage: List<&2, Evm.Slot>
  for who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  {Evm.run(Nat, Token.owner(), Evm.State{storage, who, limit, logs, world})
    == Evm.Ok{owner_of(storage), Evm.State{storage, who, limit, logs, world}} : Evm.Outcome<Nat>}

# Only the owner can hand ownership on.
law transferOwnership:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for +next: Nat
  {Evm.run(Unit, Token.transferOwnership(next), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(who, owner_of(storage)),
      Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{4n}, next} <> storage, who, limit, Evm.Log{"OwnershipTransferred(address,address)", [owner_of(storage), next], []} <> logs, world}},
      Evm.Revert{}) : Evm.Outcome<Unit>}

# EIP-2612. hashed and the signers table stand for keccak256 and ecrecover
# (see Evm.World), so these laws hold for every hash and signature table.
def hashed(world: Evm.World, +p: Evm.Preimage) -> Nat:
  Evm.hash.of(Evm.hashes.of(world), p)

def nonce(storage: List<&2, Evm.Slot>, who: Nat) -> Nat:
  Evm.lookup(storage, Evm.Mapped{Evm.Plain{3n}, who})

def separator(+world: Evm.World) -> Nat:
  hashed(world, Evm.Words{[
    hashed(world, Evm.Text{"EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"}),
    hashed(world, Evm.Text{"Bend Token"}), hashed(world, Evm.Text{"1"}), Evm.chain.of(world), Evm.self.of(world)]})

# Who signed a permit for the owner's next nonce: zero for nobody.
def permitter(+world: Evm.World, +storage: List<&2, Evm.Slot>, +owner: Nat, +spender: Nat, +value: Nat, +deadline: Nat,
  +v: Nat, +r: Nat, +s: Nat) -> Nat:
  Evm.signer.of(Evm.signers.of(world), hashed(world, Evm.Typed{separator(world), hashed(world, Evm.Words{[
    hashed(world, Evm.Text{"Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"}),
    owner, spender, value, nonce(storage, owner), deadline]})}), v, r, s)

law DOMAIN_SEPARATOR:
  for storage: List<&2, Evm.Slot>
  for who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for +world: Evm.World
  {Evm.run(Nat, Token.DOMAIN_SEPARATOR(), Evm.State{storage, who, limit, logs, world})
    == Evm.Ok{separator(world), Evm.State{storage, who, limit, logs, world}} : Evm.Outcome<Nat>}

law nonces:
  for +storage: List<&2, Evm.Slot>
  for who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for holder: Nat
  {Evm.run(Nat, Token.nonces(holder), Evm.State{storage, who, limit, logs, world})
    == Evm.Ok{nonce(storage, holder), Evm.State{storage, who, limit, logs, world}} : Evm.Outcome<Nat>}

# A permit reverts after its deadline, when the nonce overflows, and unless
# the owner signed it (a zero signer is nobody). Otherwise it uses up the
# nonce and sets the allowance, as approve does, from any caller.
law permit:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +owner: Nat
  for +spender: Nat
  for +value: Nat
  for +deadline: Nat
  for +v: Nat
  for +r: Nat
  for +s: Nat
  {Evm.run(Unit, Token.permit(owner, spender, value, deadline, v, r, s), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Bool.not(Nat.is_lt(deadline, Evm.time.of(world))),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(nonce(storage, owner), 1n), limit),
        Bool.pick(Evm.Outcome<Unit>, Bool.not(Nat.is_eq(permitter(world, storage, owner, spender, value, deadline, v, r, s), 0n)),
          Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(permitter(world, storage, owner, spender, value, deadline, v, r, s), owner),
            Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Mapped{Evm.Mapped{Evm.Plain{2n}, owner}, spender}, value}
              <> Evm.Slot{Evm.Mapped{Evm.Plain{3n}, owner}, Nat.add(nonce(storage, owner), 1n)} <> storage, who, limit,
              Evm.Log{"Approval(address,address,uint256)", [owner, spender], [value]} <> logs, world}},
            Evm.Revert{}),
          Evm.Revert{}),
        Evm.Revert{}),
      Evm.Revert{}) : Evm.Outcome<Unit>}

# Supply across calls. A Call is one call to a function that can change
# storage; the view functions change nothing (see their laws). A Tx runs a
# call in its own block: its world gives the time and the chain. A call that
# reverts keeps the state.
type Call is Data:
  Transfer{who: Nat, to: Nat, amount: Nat}
  Mint{who: Nat, to: Nat, amount: Nat}
  Approve{who: Nat, spender: Nat, amount: Nat}
  TransferFrom{who: Nat, from: Nat, to: Nat, amount: Nat}
  TransferOwnership{who: Nat, next: Nat}
  Burn{who: Nat, amount: Nat}
  Permit{who: Nat, owner: Nat, spender: Nat, value: Nat, deadline: Nat, v: Nat, r: Nat, s: Nat}

def after(-A: Data, o: Evm.Outcome<A>, s: Evm.State) -> Evm.State:
  match o:
    case Evm.Ok{_, t}:
      t
    case Evm.Revert{}:
      s

type Tx is Data:
  Tx{world: Evm.World, call: Call}

def as(+who: Nat, +world: Evm.World, s: Evm.State) -> Evm.State:
  match s:
    case Evm.State{storage, _, limit, logs, _}:
      Evm.State{storage, who, limit, logs, world}

def run(c: Call, +world: Evm.World, +s: Evm.State) -> Evm.State:
  match c:
    case Transfer{+who, +to, +amount}:
      after(Nat, Evm.run(Nat, Token.transfer(to, amount), as(who, world, s)), s)
    case Mint{+who, +to, +amount}:
      after(Unit, Evm.run(Unit, Token.mint(to, amount), as(who, world, s)), s)
    case Approve{+who, +spender, +amount}:
      after(Nat, Evm.run(Nat, Token.approve(spender, amount), as(who, world, s)), s)
    case TransferFrom{+who, +from, +to, +amount}:
      after(Nat, Evm.run(Nat, Token.transferFrom(from, to, amount), as(who, world, s)), s)
    case TransferOwnership{+who, +next}:
      after(Unit, Evm.run(Unit, Token.transferOwnership(next), as(who, world, s)), s)
    case Burn{+who, +amount}:
      after(Unit, Evm.run(Unit, Token.burn(amount), as(who, world, s)), s)
    case Permit{+who, +owner, +spender, +value, +deadline, +v, +r, +sig}:
      after(Unit, Evm.run(Unit, Token.permit(owner, spender, value, deadline, v, r, sig), as(who, world, s)), s)

def step(t: Tx, +s: Evm.State) -> Evm.State:
  match t:
    case Tx{+world, c}:
      run(c, world, s)

def trace(txs: List<&2, Tx>, +s: Evm.State) -> Evm.State:
  match txs:
    case Nil{}:
      s
    case +t <> rest:
      trace(rest, step(t, s))

# The state after `deployer` deploys the token with an initial supply.
def deployed(+deployer: Nat, +limit: Nat, +initial: Nat, +world: Evm.World) -> Evm.State:
  after(Unit, Evm.run(Unit, Token.init(initial), Evm.State{[], deployer, limit, [], world}),
    Evm.State{[], deployer, limit, [], world})

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
    case Evm.State{+storage, _, _, _, _}:
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
    case Burn{+who, _}:
      Nat.is_eq(1n, count(who, accounts))
    case _:
      True{}

def listed.tx(t: Tx, +accounts: List<&2, Nat>) -> Bool:
  match t:
    case Tx{_, c}:
      listed(c, accounts)

def all_listed(txs: List<&2, Tx>, +accounts: List<&2, Nat>) -> Bool:
  match txs:
    case Nil{}:
      True{}
    case +t <> rest:
      Bool.and(listed.tx(t, accounts), all_listed(rest, accounts))

# From deployment, after any calls by anyone in any blocks, the total supply
# is the sum of the balances of any list of accounts that has the deployer
# and every sender and receiver once. The list of every address below 2^160
# is such a list (the dispatcher rejects larger addresses), so the total
# supply is the sum of all balances. The proof does not use the limit, so it
# holds at 2^256.
law supply_sum:
  for +txs: List<&2, Tx>
  for +accounts: List<&2, Nat>
  for +deployer: Nat
  for +limit: Nat
  for +initial: Nat
  for +world: Evm.World
  for +e: {True{} == Bool.and(Nat.is_eq(1n, count(deployer, accounts)), all_listed(txs, accounts)) : Bool}
  {True{} == balanced(trace(txs, deployed(deployer, limit, initial, world)), accounts) : Bool}
