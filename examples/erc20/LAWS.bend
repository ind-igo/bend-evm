import Base
import ../../src/Evm.bend as Evm
import ../../src/sum.bend as Sum
import ./ERC20.bend as ERC20
import ./program.bend as Token

# The laws of the ERC20 core (ERC20.bend), for every token that uses it,
# then the laws of this token (program.bend). The core's laws are core.*.
#
# Each core law gives the outcome of a function from any state, with any
# continuation k: the rest of the calling function, or the end of the call.
# So a token proves a law about its own function from them, whatever it
# does before or after. Slot 0 holds the total supply, the mapping at slot
# 1 holds balances, and the mapping at slot 2 holds allowances. Storage is
# newest first, so new slots shadow old ones.
#
# The core's supply laws give what each write keeps: the total supply is
# the sum of the balances of a list of accounts in which each account that
# the write changes is once. The token's supply_sum law follows from them.

def supply(storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{0n})

def balance(storage: List<&2, Evm.Slot>, who: Nat) -> Nat:
  Evm.lookup(storage, Evm.Mapped{Evm.Plain{1n}, who})

def allowed(storage: List<&2, Evm.Slot>, holder: Nat, spender: Nat) -> Nat:
  Evm.lookup(storage, Evm.Mapped{Evm.Mapped{Evm.Plain{2n}, holder}, spender})

# The storage after each write. Storage is newest first, so new slots
# shadow old ones.
def approved(+storage: List<&2, Evm.Slot>, +holder: Nat, +spender: Nat, +amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Mapped{Evm.Plain{2n}, holder}, spender}, amount} <> storage

def debit(+storage: List<&2, Evm.Slot>, +from: Nat, amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{1n}, from}, Nat.sub(balance(storage, from), amount)} <> storage

# The receiver's balance is read after the debit, so a move to oneself
# keeps the balance.
def moved(+storage: List<&2, Evm.Slot>, +from: Nat, +to: Nat, +amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(balance(debit(storage, from, amount), to), amount)}
    <> debit(storage, from, amount)

def minted(+storage: List<&2, Evm.Slot>, +to: Nat, +amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(balance(storage, to), amount)}
    <> Evm.Slot{Evm.Plain{0n}, Nat.add(supply(storage), amount)} <> storage

def burned(+storage: List<&2, Evm.Slot>, +from: Nat, +amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Plain{0n}, Nat.sub(supply(storage), amount)} <> debit(storage, from, amount)

# The outcome of a move by who: a revert unless from's balance covers the
# amount and to's new balance is a word, else k with true.
def moving(-R: Data, k: Nat -> Evm.State -> Evm.Outcome<R>, +storage: List<&2, Evm.Slot>, who: Nat, +from: Nat, +to: Nat,
  +amount: Nat, +limit: Nat, logs: List<&2, Evm.Log>, world: Evm.World) -> Evm.Outcome<R>:
  Bool.pick(Evm.Outcome<R>, Nat.is_lt(balance(storage, from), amount),
    Evm.Revert{},
    Bool.pick(Evm.Outcome<R>, Nat.is_lt(Nat.add(balance(debit(storage, from, amount), to), amount), limit),
      k(1n, Evm.State{moved(storage, from, to, amount), who, limit, Evm.Log{"Transfer", [from, to], [amount]} <> logs, world}),
      Evm.Revert{}))

law core.totalSupply:
  for R: Data
  for k: Nat -> Evm.State -> Evm.Outcome<R>
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  {ERC20.totalSupply()(R, k, Evm.State{storage, who, limit, logs, world})
    == k(supply(storage), Evm.State{storage, who, limit, logs, world}) : Evm.Outcome<R>}

law core.balanceOf:
  for R: Data
  for k: Nat -> Evm.State -> Evm.Outcome<R>
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +holder: Nat
  {ERC20.balanceOf(holder)(R, k, Evm.State{storage, who, limit, logs, world})
    == k(balance(storage, holder), Evm.State{storage, who, limit, logs, world}) : Evm.Outcome<R>}

law core.allowance:
  for R: Data
  for k: Nat -> Evm.State -> Evm.Outcome<R>
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +holder: Nat
  for +spender: Nat
  {ERC20.allowance(holder, spender)(R, k, Evm.State{storage, who, limit, logs, world})
    == k(allowed(storage, holder, spender), Evm.State{storage, who, limit, logs, world}) : Evm.Outcome<R>}

# Approve sets the allowance, whatever it was.
law core.approve:
  for R: Data
  for k: Nat -> Evm.State -> Evm.Outcome<R>
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +spender: Nat
  for +amount: Nat
  {ERC20.approve(spender, amount)(R, k, Evm.State{storage, who, limit, logs, world})
    == k(1n, Evm.State{approved(storage, who, spender, amount), who, limit,
      Evm.Log{"Approval", [who, spender], [amount]} <> logs, world}) : Evm.Outcome<R>}

law core.move:
  for R: Data
  for k: Nat -> Evm.State -> Evm.Outcome<R>
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +from: Nat
  for +to: Nat
  for +amount: Nat
  {ERC20.move(from, to, amount)(R, k, Evm.State{storage, who, limit, logs, world})
    == moving(R, k, storage, who, from, to, amount, limit, logs, world) : Evm.Outcome<R>}

law core.transfer:
  for R: Data
  for k: Nat -> Evm.State -> Evm.Outcome<R>
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +to: Nat
  for +amount: Nat
  {ERC20.transfer(to, amount)(R, k, Evm.State{storage, who, limit, logs, world})
    == moving(R, k, storage, who, who, to, amount, limit, logs, world) : Evm.Outcome<R>}

# The caller spends from the allowance of `from`. An allowance of the
# largest word, limit - 1, is unlimited and stays as it is. Any other must
# cover the amount, and goes down by it. Then the amount moves.
law core.transferFrom:
  for R: Data
  for k: Nat -> Evm.State -> Evm.Outcome<R>
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +from: Nat
  for +to: Nat
  for +amount: Nat
  {ERC20.transferFrom(from, to, amount)(R, k, Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<R>, Nat.is_eq(allowed(storage, from, who), Nat.sub(limit, 1n)),
      moving(R, k, storage, who, from, to, amount, limit, logs, world),
      Bool.pick(Evm.Outcome<R>, Nat.is_lt(allowed(storage, from, who), amount),
        Evm.Revert{},
        moving(R, k, approved(storage, from, who, Nat.sub(allowed(storage, from, who), amount)), who, from, to, amount,
          limit, logs, world))) : Evm.Outcome<R>}

# The supply and the balance must not overflow.
law core.mint:
  for R: Data
  for k: Unit -> Evm.State -> Evm.Outcome<R>
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +to: Nat
  for +amount: Nat
  {ERC20.mint(to, amount)(R, k, Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<R>, Nat.is_lt(Nat.add(supply(storage), amount), limit),
      Bool.pick(Evm.Outcome<R>, Nat.is_lt(Nat.add(balance(storage, to), amount), limit),
        k(Unit{}, Evm.State{minted(storage, to, amount), who, limit, Evm.Log{"Transfer", [0n, to], [amount]} <> logs, world}),
        Evm.Revert{}),
      Evm.Revert{}) : Evm.Outcome<R>}

# The balance and the supply must cover the amount.
law core.burn:
  for R: Data
  for k: Unit -> Evm.State -> Evm.Outcome<R>
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +from: Nat
  for +amount: Nat
  {ERC20.burn(from, amount)(R, k, Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<R>, Nat.is_lt(balance(storage, from), amount),
      Evm.Revert{},
      Bool.pick(Evm.Outcome<R>, Nat.is_lt(supply(storage), amount),
        Evm.Revert{},
        k(Unit{}, Evm.State{burned(storage, from, amount), who, limit, Evm.Log{"Transfer", [from, 0n], [amount]} <> logs, world}))) : Evm.Outcome<R>}

# The supply laws. holdings sums the balances of a list of accounts.
def holdings(+storage: List<&2, Evm.Slot>, accounts: List<&2, Nat>) -> Nat:
  Sum.holdings(storage, 1n, accounts)

def balanced(+storage: List<&2, Evm.Slot>, +accounts: List<&2, Nat>) -> Bool:
  Nat.is_eq(supply(storage), holdings(storage, accounts))

law core.move_sum:
  for +storage: List<&2, Evm.Slot>
  for +from: Nat
  for +to: Nat
  for +amount: Nat
  for +accounts: List<&2, Nat>
  for +h: {True{} == balanced(storage, accounts) : Bool}
  for +e: {False{} == Nat.is_lt(balance(storage, from), amount) : Bool}
  for +cf: {1n == Sum.count(from, accounts) : Nat}
  for +ct: {1n == Sum.count(to, accounts) : Nat}
  {True{} == balanced(moved(storage, from, to, amount), accounts) : Bool}

law core.mint_sum:
  for +storage: List<&2, Evm.Slot>
  for +to: Nat
  for +amount: Nat
  for +accounts: List<&2, Nat>
  for +h: {True{} == balanced(storage, accounts) : Bool}
  for +c: {1n == Sum.count(to, accounts) : Nat}
  {True{} == balanced(minted(storage, to, amount), accounts) : Bool}

law core.burn_sum:
  for +storage: List<&2, Evm.Slot>
  for +from: Nat
  for +amount: Nat
  for +accounts: List<&2, Nat>
  for +h: {True{} == balanced(storage, accounts) : Bool}
  for +e: {False{} == Nat.is_lt(balance(storage, from), amount) : Bool}
  for +c: {1n == Sum.count(from, accounts) : Nat}
  {True{} == balanced(burned(storage, from, amount), accounts) : Bool}

# Writes that are not to the supply or a balance keep the sum: a plain slot
# other than 0, an entry of a mapping at a plain slot other than 1, and an
# entry of a nested mapping, such as an allowance.
law core.plain_sum:
  for +storage: List<&2, Evm.Slot>
  for +n: Nat
  for +v: Nat
  for +accounts: List<&2, Nat>
  for +h: {True{} == balanced(storage, accounts) : Bool}
  for +o: {False{} == Nat.is_eq(n, 0n) : Bool}
  {True{} == balanced(Evm.Slot{Evm.Plain{n}, v} <> storage, accounts) : Bool}

law core.mapped_sum:
  for +storage: List<&2, Evm.Slot>
  for +base: Nat
  for +x: Nat
  for +v: Nat
  for +accounts: List<&2, Nat>
  for +h: {True{} == balanced(storage, accounts) : Bool}
  for +o: {False{} == Nat.is_eq(base, 1n) : Bool}
  {True{} == balanced(Evm.Slot{Evm.Mapped{Evm.Plain{base}, x}, v} <> storage, accounts) : Bool}

law core.nested_sum:
  for +storage: List<&2, Evm.Slot>
  for +key: Evm.Key
  for +x: Nat
  for +y: Nat
  for +v: Nat
  for +accounts: List<&2, Nat>
  for +h: {True{} == balanced(storage, accounts) : Bool}
  {True{} == balanced(Evm.Slot{Evm.Mapped{Evm.Mapped{key, x}, y}, v} <> storage, accounts) : Bool}

# The token (program.bend). Each law gives every outcome from any state:
# any storage, caller, word limit, earlier logs and world, and any
# addresses. After the core's slots, the mapping at slot 3 holds nonces,
# and slot 4 holds the owner.

def owner_of(storage: List<&2, Evm.Slot>) -> Nat:
  Evm.lookup(storage, Evm.Plain{4n})

# The outcome when who moves amount from `from` to `to`, from storage: the
# end of transfer and of transferFrom.
def paid(+storage: List<&2, Evm.Slot>, who: Nat, +from: Nat, +to: Nat, +amount: Nat, +limit: Nat, logs: List<&2, Evm.Log>,
  world: Evm.World) -> Evm.Outcome<Nat>:
  moving(Nat, x => t => Evm.Ok{x, t}, storage, who, from, to, amount, limit, logs, world)

law transfer:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for +to: Nat
  for +amount: Nat
  {Evm.run(Nat, Token.transfer(to, amount), Evm.State{storage, who, limit, logs, world})
    == paid(storage, who, who, to, amount, limit, logs, world) : Evm.Outcome<Nat>}

# Only the owner can mint; others get OwnableUnauthorizedAccount. The supply
# and the balance must not overflow.
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
          Evm.Ok{Unit{}, Evm.State{minted(storage, to, amount), who, limit, Evm.Log{"Transfer", [0n, to], [amount]} <> logs, world}},
          Evm.Revert{}),
        Evm.Revert{}),
      Evm.Raise{Token.OwnableUnauthorizedAccount(who)}) : Evm.Outcome<Unit>}

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
        Evm.Ok{Unit{}, Evm.State{burned(storage, who, amount), who, limit, Evm.Log{"Transfer", [who, 0n], [amount]} <> logs, world}})) : Evm.Outcome<Unit>}

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
    == Evm.Ok{1n, Evm.State{approved(storage, who, spender, amount), who, limit, Evm.Log{"Approval", [who, spender], [amount]} <> logs, world}} : Evm.Outcome<Nat>}

# The caller spends from the allowance of `from`. An allowance of the
# largest word, limit - 1, is unlimited and stays as it is. Any other must
# cover the amount, and goes down by it. Then the amount moves as in transfer.
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
    == Bool.pick(Evm.Outcome<Nat>, Nat.is_eq(allowed(storage, from, who), Nat.sub(limit, 1n)),
      paid(storage, who, from, to, amount, limit, logs, world),
      Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(allowed(storage, from, who), amount),
        Evm.Revert{},
        paid(approved(storage, from, who, Nat.sub(allowed(storage, from, who), amount)),
          who, from, to, amount, limit, logs, world))) : Evm.Outcome<Nat>}

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
          <> Evm.Slot{Evm.Plain{0n}, Nat.add(supply(storage), initial)} <> Evm.Slot{Evm.Plain{4n}, who} <> storage, who, limit, Evm.Log{"Transfer", [0n, who], [initial]}
            <> Evm.Log{"OwnershipTransferred", [0n, who], []} <> logs, world}},
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

# Only the owner can hand ownership on; others get OwnableUnauthorizedAccount.
law transferOwnership:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for limit: Nat
  for logs: List<&2, Evm.Log>
  for world: Evm.World
  for +next: Nat
  {Evm.run(Unit, Token.transferOwnership(next), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(who, owner_of(storage)),
      Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{4n}, next} <> storage, who, limit, Evm.Log{"OwnershipTransferred", [owner_of(storage), next], []} <> logs, world}},
      Evm.Raise{Token.OwnableUnauthorizedAccount(who)}) : Evm.Outcome<Unit>}

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

# A permit reverts after its deadline with ERC2612ExpiredSignature, when the
# nonce overflows, and unless the owner signed it (a zero signer is nobody)
# with ERC2612InvalidSigner. Otherwise it uses up the
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
              Evm.Log{"Approval", [owner, spender], [value]} <> logs, world}},
            Evm.Raise{Token.ERC2612InvalidSigner(permitter(world, storage, owner, spender, value, deadline, v, r, s), owner)}),
          Evm.Raise{Token.ERC2612InvalidSigner(permitter(world, storage, owner, spender, value, deadline, v, r, s), owner)}),
        Evm.Revert{}),
      Evm.Raise{Token.ERC2612ExpiredSignature(deadline)}) : Evm.Outcome<Unit>}

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
    case Evm.Raise{_}:
      s
    case Evm.Calling{_, _, _}:
      s

type Tx is Data:
  Tx{world: Evm.World, call: Call}

# The state s as a call from who sees it, in world.
def called(+who: Nat, +world: Evm.World, s: Evm.State) -> Evm.State:
  match s:
    case Evm.State{storage, _, limit, logs, _}:
      Evm.State{storage, who, limit, logs, world}

def run(c: Call, +world: Evm.World, +s: Evm.State) -> Evm.State:
  match c:
    case Transfer{+who, +to, +amount}:
      after(Nat, Evm.run(Nat, Token.transfer(to, amount), called(who, world, s)), s)
    case Mint{+who, +to, +amount}:
      after(Unit, Evm.run(Unit, Token.mint(to, amount), called(who, world, s)), s)
    case Approve{+who, +spender, +amount}:
      after(Nat, Evm.run(Nat, Token.approve(spender, amount), called(who, world, s)), s)
    case TransferFrom{+who, +from, +to, +amount}:
      after(Nat, Evm.run(Nat, Token.transferFrom(from, to, amount), called(who, world, s)), s)
    case TransferOwnership{+who, +next}:
      after(Unit, Evm.run(Unit, Token.transferOwnership(next), called(who, world, s)), s)
    case Burn{+who, +amount}:
      after(Unit, Evm.run(Unit, Token.burn(amount), called(who, world, s)), s)
    case Permit{+who, +owner, +spender, +value, +deadline, +v, +r, +sig}:
      after(Unit, Evm.run(Unit, Token.permit(owner, spender, value, deadline, v, r, sig), called(who, world, s)), s)

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

def balanced.at(s: Evm.State, +accounts: List<&2, Nat>) -> Bool:
  match s:
    case Evm.State{storage, _, _, _, _}:
      balanced(storage, accounts)

# Each account whose balance the call can change is in the list once.
def listed(c: Call, +accounts: List<&2, Nat>) -> Bool:
  match c:
    case Transfer{+who, +to, _}:
      Bool.and(Nat.is_eq(1n, Sum.count(who, accounts)), Nat.is_eq(1n, Sum.count(to, accounts)))
    case Mint{_, +to, _}:
      Nat.is_eq(1n, Sum.count(to, accounts))
    case TransferFrom{_, +from, +to, _}:
      Bool.and(Nat.is_eq(1n, Sum.count(from, accounts)), Nat.is_eq(1n, Sum.count(to, accounts)))
    case Burn{+who, _}:
      Nat.is_eq(1n, Sum.count(who, accounts))
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
  for +e: {True{} == Bool.and(Nat.is_eq(1n, Sum.count(deployer, accounts)), all_listed(txs, accounts)) : Bool}
  {True{} == balanced.at(trace(txs, deployed(deployer, limit, initial, world)), accounts) : Bool}
