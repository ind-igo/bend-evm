import Base
import ../src/Evm.bend as Evm
import ../src/sum.bend as Sum
import ./ERC20.bend as ERC20

# Laws of the ERC20 core, for every token that uses it. Each law gives the
# outcome of a function from any state, with any continuation k: the rest
# of the calling function, or the end of the call. So a token proves a law
# about its own function from these laws, whatever it does before or after.
#
# The supply laws give what each write keeps: the total supply is the sum
# of the balances of a list of accounts in which each account that the
# write changes is once. A token proves its own supply law from them, and
# from the laws for writes to its own slots (see examples/token).

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

law totalSupply:
  for R: Data
  for k: Nat -> Evm.State -> Evm.Outcome<R>
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  {ERC20.totalSupply()(R, k, Evm.State{storage, who, limit, logs, world})
    == k(supply(storage), Evm.State{storage, who, limit, logs, world}) : Evm.Outcome<R>}

law balanceOf:
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

law allowance:
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
law approve:
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

law move:
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

law transfer:
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
law transferFrom:
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
law mint:
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
law burn:
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

law move_sum:
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

law mint_sum:
  for +storage: List<&2, Evm.Slot>
  for +to: Nat
  for +amount: Nat
  for +accounts: List<&2, Nat>
  for +h: {True{} == balanced(storage, accounts) : Bool}
  for +c: {1n == Sum.count(to, accounts) : Nat}
  {True{} == balanced(minted(storage, to, amount), accounts) : Bool}

law burn_sum:
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
law plain_sum:
  for +storage: List<&2, Evm.Slot>
  for +n: Nat
  for +v: Nat
  for +accounts: List<&2, Nat>
  for +h: {True{} == balanced(storage, accounts) : Bool}
  for +o: {False{} == Nat.is_eq(n, 0n) : Bool}
  {True{} == balanced(Evm.Slot{Evm.Plain{n}, v} <> storage, accounts) : Bool}

law mapped_sum:
  for +storage: List<&2, Evm.Slot>
  for +base: Nat
  for +x: Nat
  for +v: Nat
  for +accounts: List<&2, Nat>
  for +h: {True{} == balanced(storage, accounts) : Bool}
  for +o: {False{} == Nat.is_eq(base, 1n) : Bool}
  {True{} == balanced(Evm.Slot{Evm.Mapped{Evm.Plain{base}, x}, v} <> storage, accounts) : Bool}

law nested_sum:
  for +storage: List<&2, Evm.Slot>
  for +key: Evm.Key
  for +x: Nat
  for +y: Nat
  for +v: Nat
  for +accounts: List<&2, Nat>
  for +h: {True{} == balanced(storage, accounts) : Bool}
  {True{} == balanced(Evm.Slot{Evm.Mapped{Evm.Mapped{key, x}, y}, v} <> storage, accounts) : Bool}
