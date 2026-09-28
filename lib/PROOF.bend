import Base
import ../src/Evm.bend as Evm
import ../src/nat.bend as N
import ../src/sum.bend as Sum
import ./LAWS.bend as Laws
import ./ERC20.bend as ERC20

def Laws.totalSupply(R, k, storage, who, limit, logs, world):
  {==}

def Laws.balanceOf(R, k, storage, who, limit, logs, world, holder):
  {==}

def Laws.allowance(R, k, storage, who, limit, logs, world, holder, spender):
  {==}

def Laws.approve(R, k, storage, who, limit, logs, world, spender, amount):
  {==}

def Laws.move(R, k, storage, who, limit, logs, world, from, to, amount):
  {==}

def Laws.transfer(R, k, storage, who, limit, logs, world, to, amount):
  {==}

# A run stops at a branch on a value that is not known, so the proof
# matches on it.
def branched(-A: Data, -R: Data, c: Bool, -a: Evm.Contract(A), -b: Evm.Contract(A), -k: A -> Evm.State -> Evm.Outcome<R>,
  -s: Evm.State) ->
  {Evm.branch(A, c, a, b)(R, k, s) == Bool.pick(Evm.Outcome<R>, c, a(R, k, s), b(R, k, s)) : Evm.Outcome<R>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.transferFrom(R, k, storage, who, limit, logs, world, from, to, amount):
  +allowed = Laws.allowed(storage, from, who)
  branched(Nat, R, Nat.is_eq(allowed, Nat.sub(limit, 1n)), ERC20.move(from, to, amount),
    do Evm.Contract<Nat>:
      left : Nat <- Evm.sub(allowed, amount)
      Evm.store2(ERC20.ALLOWANCES(), from, who, left)
      ERC20.move(from, to, amount),
    k, Evm.State{storage, who, limit, logs, world})

def Laws.mint(R, k, storage, who, limit, logs, world, to, amount):
  {==}

def Laws.burn(R, k, storage, who, limit, logs, world, from, amount):
  {==}

def Laws.move_sum(storage, from, to, amount, accounts, h, e, cf, ct):
  %Equal.trans(Nat, Laws.holdings(storage, accounts), Nat.add(Laws.holdings(Laws.debit(storage, from, amount), accounts), amount),
    Laws.holdings(Laws.moved(storage, from, to, amount), accounts),
    Equal.sym(Nat, Nat.add(Laws.holdings(Laws.debit(storage, from, amount), accounts), amount), Laws.holdings(storage, accounts),
      Sum.debit_once(storage, 1n, from, amount, accounts, e, cf)),
    Sum.credit_once(Laws.debit(storage, from, amount), 1n, to, amount, accounts, ct)) :
    {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

def Laws.mint_sum(storage, to, amount, accounts, h, c):
  %Sum.credit_once(Evm.Slot{Evm.Plain{0n}, Nat.add(Laws.supply(storage), amount)} <> storage, 1n, to, amount, accounts, c) :
    {True{} == Nat.is_eq(Nat.add(Laws.supply(storage), amount), _) : Bool}
  %Sum.skip_plain(storage, 1n, 0n, Nat.add(Laws.supply(storage), amount), accounts) :
    {True{} == Nat.is_eq(Nat.add(Laws.supply(storage), amount), Nat.add(_, amount)) : Bool}
  %N.eq_sound(Laws.supply(storage), Laws.holdings(storage, accounts), h) :
    {True{} == Nat.is_eq(Nat.add(Laws.supply(storage), amount), Nat.add(_, amount)) : Bool}
  N.eq_refl(Nat.add(Laws.supply(storage), amount))

def Laws.burn_sum(storage, from, amount, accounts, h, e, c):
  %Sum.skip_plain(Laws.debit(storage, from, amount), 1n, 0n, Nat.sub(Laws.supply(storage), amount), accounts) :
    {True{} == Nat.is_eq(Nat.sub(Laws.supply(storage), amount), _) : Bool}
  %Equal.sym(Nat, Laws.supply(storage), Laws.holdings(storage, accounts),
    N.eq_sound(Laws.supply(storage), Laws.holdings(storage, accounts), h)) :
    {True{} == Nat.is_eq(Nat.sub(_, amount), Laws.holdings(Laws.debit(storage, from, amount), accounts)) : Bool}
  %Sum.debit_once(storage, 1n, from, amount, accounts, e, c) :
    {True{} == Nat.is_eq(Nat.sub(_, amount), Laws.holdings(Laws.debit(storage, from, amount), accounts)) : Bool}
  %N.add_comm(amount, Laws.holdings(Laws.debit(storage, from, amount), accounts)) :
    {True{} == Nat.is_eq(Nat.sub(_, amount), Laws.holdings(Laws.debit(storage, from, amount), accounts)) : Bool}
  %N.sub_add_cancel(Laws.holdings(Laws.debit(storage, from, amount), accounts), amount) :
    {True{} == Nat.is_eq(_, Laws.holdings(Laws.debit(storage, from, amount), accounts)) : Bool}
  N.eq_refl(Laws.holdings(Laws.debit(storage, from, amount), accounts))

def Laws.plain_sum(storage, n, v, accounts, h, o):
  %o : {True{} == Nat.is_eq(Bool.pick(Nat, _, v, Laws.supply(storage)),
    Laws.holdings(Evm.Slot{Evm.Plain{n}, v} <> storage, accounts)) : Bool}
  %Sum.skip_plain(storage, 1n, n, v, accounts) : {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

def Laws.mapped_sum(storage, base, x, v, accounts, h, o):
  %Sum.skip_mapped(storage, 1n, base, x, v, accounts, o) : {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

def Laws.nested_sum(storage, key, x, y, v, accounts, h):
  %Sum.skip_nested(storage, 1n, key, x, y, v, accounts) : {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h
