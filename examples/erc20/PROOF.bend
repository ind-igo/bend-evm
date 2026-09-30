import Base
import ../../src/Evm.bend as Evm
import ../../src/nat.bend as N
import ../../src/sum.bend as Sum
import ./LAWS.bend as Laws
import ./ERC20.bend as ERC20
import ./Token.bend as Token

# The core's laws.

def Laws.core.totalSupply(R, k, storage, who, limit, logs, world):
  {==}

def Laws.core.balanceOf(R, k, storage, who, limit, logs, world, holder):
  {==}

def Laws.core.allowance(R, k, storage, who, limit, logs, world, holder, spender):
  {==}

def Laws.core.approve(R, k, storage, who, limit, logs, world, spender, amount):
  {==}

def Laws.core.move(R, k, storage, who, limit, logs, world, from, to, amount):
  {==}

def Laws.core.transfer(R, k, storage, who, limit, logs, world, to, amount):
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

def Laws.core.transferFrom(R, k, storage, who, limit, logs, world, from, to, amount):
  +allowed = Laws.allowed(storage, from, who)
  branched(Nat, R, Nat.is_eq(allowed, Nat.sub(limit, 1n)), ERC20.move(from, to, amount),
    do Evm.Contract<Nat>:
      left : Nat <- Evm.sub(allowed, amount)
      Evm.store2(ERC20.ALLOWANCES(), from, who, left)
      ERC20.move(from, to, amount),
    k, Evm.State{storage, who, limit, logs, world})

def Laws.core.mint(R, k, storage, who, limit, logs, world, to, amount):
  {==}

def Laws.core.burn(R, k, storage, who, limit, logs, world, from, amount):
  {==}

def Laws.core.move_sum(storage, from, to, amount, accounts, h, e, cf, ct):
  %Equal.trans(Nat, Laws.holdings(storage, accounts), Nat.add(Laws.holdings(Laws.debit(storage, from, amount), accounts), amount),
    Laws.holdings(Laws.moved(storage, from, to, amount), accounts),
    Equal.sym(Nat, Nat.add(Laws.holdings(Laws.debit(storage, from, amount), accounts), amount), Laws.holdings(storage, accounts),
      Sum.debit_once(storage, 1n, from, amount, accounts, e, cf)),
    Sum.credit_once(Laws.debit(storage, from, amount), 1n, to, amount, accounts, ct)) :
    {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

def Laws.core.mint_sum(storage, to, amount, accounts, h, c):
  %Sum.credit_once(Evm.Slot{Evm.Plain{0n}, Nat.add(Laws.supply(storage), amount)} <> storage, 1n, to, amount, accounts, c) :
    {True{} == Nat.is_eq(Nat.add(Laws.supply(storage), amount), _) : Bool}
  %Sum.skip_plain(storage, 1n, 0n, Nat.add(Laws.supply(storage), amount), accounts) :
    {True{} == Nat.is_eq(Nat.add(Laws.supply(storage), amount), Nat.add(_, amount)) : Bool}
  %N.eq_sound(Laws.supply(storage), Laws.holdings(storage, accounts), h) :
    {True{} == Nat.is_eq(Nat.add(Laws.supply(storage), amount), Nat.add(_, amount)) : Bool}
  N.eq_refl(Nat.add(Laws.supply(storage), amount))

def Laws.core.burn_sum(storage, from, amount, accounts, h, e, c):
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

def Laws.core.plain_sum(storage, n, v, accounts, h, o):
  %o : {True{} == Nat.is_eq(Bool.pick(Nat, _, v, Laws.supply(storage)),
    Laws.holdings(Evm.Slot{Evm.Plain{n}, v} <> storage, accounts)) : Bool}
  %Sum.skip_plain(storage, 1n, n, v, accounts) : {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

def Laws.core.mapped_sum(storage, base, x, v, accounts, h, o):
  %Sum.skip_mapped(storage, 1n, base, x, v, accounts, o) : {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

def Laws.core.nested_sum(storage, key, x, y, v, accounts, h):
  %Sum.skip_nested(storage, 1n, key, x, y, v, accounts) : {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

# The token's laws.

def Laws.transfer(storage, who, limit, logs, world, to, amount):
  {==}

def Laws.mint(storage, who, limit, logs, world, to, amount):
  {==}

def Laws.DOMAIN_SEPARATOR(storage, who, limit, logs, world):
  {==}

def Laws.nonces(storage, who, limit, logs, world, holder):
  {==}

def Laws.permit(storage, who, limit, logs, world, owner, spender, value, deadline, v, r, s):
  {==}

def Laws.burn(storage, who, limit, logs, world, amount):
  {==}

def Laws.allowance(storage, who, limit, logs, world, holder, spender):
  {==}

def Laws.approve(storage, who, limit, logs, world, spender, amount):
  {==}

# The run stops at the branch on the allowance; the core's law has both arms.
def Laws.transferFrom(storage, who, limit, logs, world, from, to, amount):
  Laws.core.transferFrom(Nat, x => t => Evm.Ok{x, t}, storage, who, limit, logs, world, from, to, amount)

def Laws.init(storage, who, limit, logs, world, initial):
  {==}

def Laws.owner(storage, who, limit, logs, world):
  {==}

def Laws.transferOwnership(storage, who, limit, logs, world, next):
  {==}

# The supply law. The core's supply laws give what each of its writes, and
# each write to the token's own slots, does to the sum; the lemmas below
# give the invariant for each call.

def keep_pick(-A: Data, +c: Bool, -a: Evm.Outcome<A>, -b: Evm.Outcome<A>, -s: Evm.State, -accounts: List<&2, Nat>,
  ha: {True{} == c : Bool} -> {True{} == Laws.balanced.at(Laws.after(A, a, s), accounts) : Bool},
  hb: {False{} == c : Bool} -> {True{} == Laws.balanced.at(Laws.after(A, b, s), accounts) : Bool}) ->
  {True{} == Laws.balanced.at(Laws.after(A, Bool.pick(Evm.Outcome<A>, c, a, b), s), accounts) : Bool}:
  match c:
    case True{}:
      ha({==})
    case False{}:
      hb({==})

def keeps.mint(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +to: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Laws.balanced(storage, accounts) : Bool},
  +ct: {1n == Sum.count(to, accounts) : Nat}) ->
  {True{} == Laws.balanced.at(Laws.step(Laws.Tx{world, Laws.Mint{who, to, amount}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  keep_pick(Unit, Nat.is_eq(who, Evm.lookup(storage, Evm.Plain{4n})),
    Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.supply(storage), amount), limit),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.balance(storage, to), amount), limit),
        Evm.Ok{Unit{}, Evm.State{Laws.minted(storage, to, amount), who, limit, Evm.Log{"Transfer", [0n, to], [amount]} <> logs, world}}, Evm.Revert{}),
      Evm.Revert{}),
    Evm.Raise{Token.OwnableUnauthorizedAccount(who)}, Evm.State{storage, caller, limit, logs, old}, accounts,
    _ => keep_pick(Unit, Nat.is_lt(Nat.add(Laws.supply(storage), amount), limit),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.balance(storage, to), amount), limit),
        Evm.Ok{Unit{}, Evm.State{Laws.minted(storage, to, amount), who, limit, Evm.Log{"Transfer", [0n, to], [amount]} <> logs, world}}, Evm.Revert{}),
      Evm.Revert{}, Evm.State{storage, caller, limit, logs, old}, accounts,
      _ => keep_pick(Unit, Nat.is_lt(Nat.add(Laws.balance(storage, to), amount), limit),
        Evm.Ok{Unit{}, Evm.State{Laws.minted(storage, to, amount), who, limit, Evm.Log{"Transfer", [0n, to], [amount]} <> logs, world}}, Evm.Revert{},
        Evm.State{storage, caller, limit, logs, old}, accounts,
        _ => Laws.core.mint_sum(storage, to, amount, accounts, h, ct),
        _ => h),
      _ => h),
    _ => h)

def keeps.approve(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +spender: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Laws.balanced(storage, accounts) : Bool}) ->
  {True{} == Laws.balanced.at(Laws.step(Laws.Tx{world, Laws.Approve{who, spender, amount}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  Laws.core.nested_sum(storage, Evm.Plain{2n}, who, spender, amount, accounts, h)

def keeps.transferOwnership(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +next: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Laws.balanced(storage, accounts) : Bool}) ->
  {True{} == Laws.balanced.at(Laws.step(Laws.Tx{world, Laws.TransferOwnership{who, next}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  keep_pick(Unit, Nat.is_eq(who, Evm.lookup(storage, Evm.Plain{4n})),
    Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{4n}, next} <> storage, who, limit, Evm.Log{"OwnershipTransferred", [Evm.lookup(storage, Evm.Plain{4n}), next], []} <> logs, world}},
    Evm.Raise{Token.OwnableUnauthorizedAccount(who)}, Evm.State{storage, caller, limit, logs, old}, accounts,
    _ => Laws.core.plain_sum(storage, 4n, next, accounts, h, {==}),
    _ => h)

# A law's outcome can stand for the run it equals.
def keep_eq(-A: Data, -x: Evm.Outcome<A>, -y: Evm.Outcome<A>, -s: Evm.State, -accounts: List<&2, Nat>,
  e: {x == y : Evm.Outcome<A>}, h: {True{} == Laws.balanced.at(Laws.after(A, y, s), accounts) : Bool}) ->
  {True{} == Laws.balanced.at(Laws.after(A, x, s), accounts) : Bool}:
  %Equal.sym(Evm.Outcome<A>, x, y, e) : {True{} == Laws.balanced.at(Laws.after(A, _, s), accounts) : Bool}
  h

# The end of transferFrom from storage st keeps the sum when st does: a
# revert keeps s, and s is balanced.
def keeps.paid(+st: List<&2, Evm.Slot>, +who: Nat, +from: Nat, +to: Nat, +amount: Nat, +limit: Nat,
  +logs: List<&2, Evm.Log>, +world: Evm.World, -s: Evm.State, +accounts: List<&2, Nat>,
  +hs: {True{} == Laws.balanced.at(s, accounts) : Bool},
  +hx: {True{} == Laws.balanced(st, accounts) : Bool},
  +cf: {1n == Sum.count(from, accounts) : Nat}, +ct: {1n == Sum.count(to, accounts) : Nat}) ->
  {True{} == Laws.balanced.at(Laws.after(Nat, Laws.paid(st, who, from, to, amount, limit, logs, world), s), accounts) : Bool}:
  keep_pick(Nat, Nat.is_lt(Laws.balance(st, from), amount), Evm.Revert{},
    Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(Nat.add(Laws.balance(Laws.debit(st, from, amount), to), amount), limit),
      Evm.Ok{1n, Evm.State{Laws.moved(st, from, to, amount), who, limit, Evm.Log{"Transfer", [from, to], [amount]} <> logs, world}}, Evm.Revert{}),
    s, accounts,
    _ => hs,
    e => keep_pick(Nat, Nat.is_lt(Nat.add(Laws.balance(Laws.debit(st, from, amount), to), amount), limit),
      Evm.Ok{1n, Evm.State{Laws.moved(st, from, to, amount), who, limit, Evm.Log{"Transfer", [from, to], [amount]} <> logs, world}}, Evm.Revert{},
      s, accounts,
      _ => Laws.core.move_sum(st, from, to, amount, accounts, hx, e, cf, ct),
      _ => hs))

def keeps.transfer(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +to: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Laws.balanced(storage, accounts) : Bool},
  +cf: {1n == Sum.count(who, accounts) : Nat}, +ct: {1n == Sum.count(to, accounts) : Nat}) ->
  {True{} == Laws.balanced.at(Laws.step(Laws.Tx{world, Laws.Transfer{who, to, amount}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  keeps.paid(storage, who, who, to, amount, limit, logs, world, Evm.State{storage, caller, limit, logs, old}, accounts, h, h, cf, ct)

def keeps.transferFrom(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +from: Nat, +to: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Laws.balanced(storage, accounts) : Bool},
  +cf: {1n == Sum.count(from, accounts) : Nat}, +ct: {1n == Sum.count(to, accounts) : Nat}) ->
  {True{} == Laws.balanced.at(Laws.step(Laws.Tx{world, Laws.TransferFrom{who, from, to, amount}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  +s = {Evm.State{storage, caller, limit, logs, old} : Evm.State}
  +low = Laws.approved(storage, from, who, Nat.sub(Laws.allowed(storage, from, who), amount))
  keep_eq(Nat, Evm.run(Nat, Token.transferFrom(from, to, amount), Evm.State{storage, who, limit, logs, world}),
    Bool.pick(Evm.Outcome<Nat>, Nat.is_eq(Laws.allowed(storage, from, who), Nat.sub(limit, 1n)),
      Laws.paid(storage, who, from, to, amount, limit, logs, world),
      Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(Laws.allowed(storage, from, who), amount), Evm.Revert{},
        Laws.paid(low, who, from, to, amount, limit, logs, world))),
    s, accounts, Laws.transferFrom(storage, who, limit, logs, world, from, to, amount),
    keep_pick(Nat, Nat.is_eq(Laws.allowed(storage, from, who), Nat.sub(limit, 1n)),
      Laws.paid(storage, who, from, to, amount, limit, logs, world),
      Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(Laws.allowed(storage, from, who), amount), Evm.Revert{},
        Laws.paid(low, who, from, to, amount, limit, logs, world)),
      s, accounts,
      _ => keeps.paid(storage, who, from, to, amount, limit, logs, world, s, accounts, h, h, cf, ct),
      _ => keep_pick(Nat, Nat.is_lt(Laws.allowed(storage, from, who), amount), Evm.Revert{},
        Laws.paid(low, who, from, to, amount, limit, logs, world), s, accounts,
        _ => h,
        _ => keeps.paid(low, who, from, to, amount, limit, logs, world, s, accounts, h,
          Laws.core.nested_sum(storage, Evm.Plain{2n}, from, who, Nat.sub(Laws.allowed(storage, from, who), amount), accounts, h),
          cf, ct))))

def keeps.burn(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Laws.balanced(storage, accounts) : Bool},
  +c: {1n == Sum.count(who, accounts) : Nat}) ->
  {True{} == Laws.balanced.at(Laws.step(Laws.Tx{world, Laws.Burn{who, amount}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  keep_pick(Unit, Nat.is_lt(Laws.balance(storage, who), amount), Evm.Revert{},
    Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Laws.supply(storage), amount), Evm.Revert{},
      Evm.Ok{Unit{}, Evm.State{Laws.burned(storage, who, amount), who, limit, Evm.Log{"Transfer", [who, 0n], [amount]} <> logs, world}}),
    Evm.State{storage, caller, limit, logs, old}, accounts,
    _ => h,
    e => keep_pick(Unit, Nat.is_lt(Laws.supply(storage), amount), Evm.Revert{},
      Evm.Ok{Unit{}, Evm.State{Laws.burned(storage, who, amount), who, limit, Evm.Log{"Transfer", [who, 0n], [amount]} <> logs, world}},
      Evm.State{storage, caller, limit, logs, old}, accounts,
      _ => h,
      _ => Laws.core.burn_sum(storage, who, amount, accounts, h, e, c)))

def permitted(+storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  +owner: Nat, +spender: Nat, +value: Nat) -> Evm.Outcome<Unit>:
  Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Mapped{Evm.Mapped{Evm.Plain{2n}, owner}, spender}, value}
    <> Evm.Slot{Evm.Mapped{Evm.Plain{3n}, owner}, Nat.add(Laws.nonce(storage, owner), 1n)} <> storage, who, limit,
    Evm.Log{"Approval", [owner, spender], [value]} <> logs, world}}

def ok.permit(+storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  +owner: Nat, +spender: Nat, +value: Nat, -s: Evm.State, +accounts: List<&2, Nat>,
  +h: {True{} == Laws.balanced(storage, accounts) : Bool}) ->
  {True{} == Laws.balanced.at(Laws.after(Unit, permitted(storage, who, limit, logs, world, owner, spender, value), s), accounts) : Bool}:
  Laws.core.nested_sum(Evm.Slot{Evm.Mapped{Evm.Plain{3n}, owner}, Nat.add(Laws.nonce(storage, owner), 1n)} <> storage, Evm.Plain{2n},
    owner, spender, value, accounts,
    Laws.core.mapped_sum(storage, 3n, owner, Nat.add(Laws.nonce(storage, owner), 1n), accounts, h, {==}))

def keeps.permit(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World,
  +world: Evm.World, +who: Nat, +owner: Nat, +spender: Nat, +value: Nat, +deadline: Nat, +v: Nat, +r: Nat, +sig: Nat,
  +accounts: List<&2, Nat>, +h: {True{} == Laws.balanced(storage, accounts) : Bool}) ->
  {True{} == Laws.balanced.at(Laws.step(Laws.Tx{world, Laws.Permit{who, owner, spender, value, deadline, v, r, sig}},
    Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  +signer = Laws.permitter(world, storage, owner, spender, value, deadline, v, r, sig)
  -ok = permitted(storage, who, limit, logs, world, owner, spender, value)
  +before = {Evm.State{storage, caller, limit, logs, old} : Evm.State}
  -bad = {Evm.Raise{Token.ERC2612InvalidSigner(signer, owner)} : Evm.Outcome<Unit>}
  -late = {Evm.Raise{Token.ERC2612ExpiredSignature(deadline)} : Evm.Outcome<Unit>}
  -d = Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(signer, owner), ok, bad)
  -c = Bool.pick(Evm.Outcome<Unit>, Bool.not(Nat.is_eq(signer, 0n)), d, bad)
  -b = Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.nonce(storage, owner), 1n), limit), c, Evm.Revert{})
  keep_pick(Unit, Bool.not(Nat.is_lt(deadline, Evm.time.of(world))), b, late, before, accounts,
    _ => keep_pick(Unit, Nat.is_lt(Nat.add(Laws.nonce(storage, owner), 1n), limit), c, Evm.Revert{}, before, accounts,
      _ => keep_pick(Unit, Bool.not(Nat.is_eq(signer, 0n)), d, bad, before, accounts,
        _ => keep_pick(Unit, Nat.is_eq(signer, owner), ok, bad, before, accounts,
          _ => ok.permit(storage, who, limit, logs, world, owner, spender, value, before, accounts, h),
          _ => h),
        _ => h),
      _ => h),
    _ => h)

def once(+who: Nat, +accounts: List<&2, Nat>, +e: {True{} == Nat.is_eq(1n, Sum.count(who, accounts)) : Bool}) ->
  {1n == Sum.count(who, accounts) : Nat}:
  N.eq_sound(1n, Sum.count(who, accounts), e)

def keeps.step(+t: Laws.Tx, +s: Evm.State, +accounts: List<&2, Nat>, +h: {True{} == Laws.balanced.at(s, accounts) : Bool},
  +l: {True{} == Laws.listed.tx(t, accounts) : Bool}) -> {True{} == Laws.balanced.at(Laws.step(t, s), accounts) : Bool}:
  match t s:
    case Laws.Tx{+world, Laws.Transfer{+who, +to, +amount}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.transfer(storage, caller, limit, logs, old, world, who, to, amount, accounts, h,
        once(who, accounts, N.and_left(Nat.is_eq(1n, Sum.count(who, accounts)), Nat.is_eq(1n, Sum.count(to, accounts)), l)),
        once(to, accounts, N.and_right(Nat.is_eq(1n, Sum.count(who, accounts)), Nat.is_eq(1n, Sum.count(to, accounts)), l)))
    case Laws.Tx{+world, Laws.Mint{+who, +to, +amount}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.mint(storage, caller, limit, logs, old, world, who, to, amount, accounts, h, once(to, accounts, l))
    case Laws.Tx{+world, Laws.Approve{+who, +spender, +amount}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.approve(storage, caller, limit, logs, old, world, who, spender, amount, accounts, h)
    case Laws.Tx{+world, Laws.TransferFrom{+who, +from, +to, +amount}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.transferFrom(storage, caller, limit, logs, old, world, who, from, to, amount, accounts, h,
        once(from, accounts, N.and_left(Nat.is_eq(1n, Sum.count(from, accounts)), Nat.is_eq(1n, Sum.count(to, accounts)), l)),
        once(to, accounts, N.and_right(Nat.is_eq(1n, Sum.count(from, accounts)), Nat.is_eq(1n, Sum.count(to, accounts)), l)))
    case Laws.Tx{+world, Laws.TransferOwnership{+who, +next}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.transferOwnership(storage, caller, limit, logs, old, world, who, next, accounts, h)
    case Laws.Tx{+world, Laws.Permit{+who, +owner, +spender, +value, +deadline, +v, +r, +sig}}
      Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.permit(storage, caller, limit, logs, old, world, who, owner, spender, value, deadline, v, r, sig, accounts, h)
    case Laws.Tx{+world, Laws.Burn{+who, +amount}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.burn(storage, caller, limit, logs, old, world, who, amount, accounts, h, once(who, accounts, l))

def keeps.trace(+calls: List<&2, Laws.Tx>, +s: Evm.State, +accounts: List<&2, Nat>, +h: {True{} == Laws.balanced.at(s, accounts) : Bool},
  +l: {True{} == Laws.all_listed(calls, accounts) : Bool}) -> {True{} == Laws.balanced.at(Laws.trace(calls, s), accounts) : Bool}:
  match calls:
    case Nil{}:
      h
    case +c <> +rest:
      keeps.trace(rest, Laws.step(c, s), accounts,
        keeps.step(c, s, accounts, h, N.and_left(Laws.listed.tx(c, accounts), Laws.all_listed(rest, accounts), l)),
        N.and_right(Laws.listed.tx(c, accounts), Laws.all_listed(rest, accounts), l))

def init_sum(+deployer: Nat, +initial: Nat, +accounts: List<&2, Nat>) ->
  {Sum.hits(deployer, initial, accounts) == Laws.holdings(Evm.Slot{Evm.Mapped{Evm.Plain{1n}, deployer}, initial}
    <> Evm.Slot{Evm.Plain{0n}, initial} <> Evm.Slot{Evm.Plain{4n}, deployer} <> [], accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      %init_sum(deployer, initial, rest) : {Nat.add(Sum.gain(deployer, initial, a), Sum.hits(deployer, initial, rest))
        == Nat.add(Sum.gain(deployer, initial, a), _) : Nat}
      {==}

def init_storage(+deployer: Nat, +initial: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{1n}, deployer}, initial} <> Evm.Slot{Evm.Plain{0n}, initial}
    <> Evm.Slot{Evm.Plain{4n}, deployer} <> []

def init_ok(+deployer: Nat, +limit: Nat, +initial: Nat, +world: Evm.World) -> Evm.Outcome<Unit>:
  Evm.Ok{Unit{}, Evm.State{init_storage(deployer, initial), deployer, limit, [Evm.Log{"Transfer", [0n, deployer], [initial]},
      Evm.Log{"OwnershipTransferred", [0n, deployer], []}], world}}

def ok.init(+deployer: Nat, +limit: Nat, +initial: Nat, +world: Evm.World, +accounts: List<&2, Nat>,
  +c: {1n == Sum.count(deployer, accounts) : Nat}) ->
  {True{} == Laws.balanced.at(Laws.after(Unit, init_ok(deployer, limit, initial, world), Evm.State{[], deployer, limit, [], world}), accounts) : Bool}:
  %init_sum(deployer, initial, accounts) : {True{} == Nat.is_eq(initial, _) : Bool}
  %Sum.hits_once(deployer, initial, accounts, c) : {True{} == Nat.is_eq(initial, _) : Bool}
  N.eq_refl(initial)

# No account holds anything in empty storage.
def holdings_empty(+accounts: List<&2, Nat>) -> {0n == Laws.holdings([], accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      holdings_empty(rest)

def empty(+deployer: Nat, +limit: Nat, +world: Evm.World, +accounts: List<&2, Nat>) ->
  {True{} == Laws.balanced.at(Evm.State{[], deployer, limit, [], world}, accounts) : Bool}:
  %holdings_empty(accounts) : {True{} == Nat.is_eq(0n, _) : Bool}
  {==}

# Deployment mints the initial supply to the deployer, or reverts.
def keeps.init(+deployer: Nat, +limit: Nat, +initial: Nat, +world: Evm.World, +accounts: List<&2, Nat>,
  +c: {1n == Sum.count(deployer, accounts) : Nat}) -> {True{} == Laws.balanced.at(Laws.deployed(deployer, limit, initial, world), accounts) : Bool}:
  keep_pick(Unit, Nat.is_lt(initial, limit),
    Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(initial, limit), init_ok(deployer, limit, initial, world), Evm.Revert{}), Evm.Revert{},
    Evm.State{[], deployer, limit, [], world}, accounts,
    _ => keep_pick(Unit, Nat.is_lt(initial, limit), init_ok(deployer, limit, initial, world), Evm.Revert{},
      Evm.State{[], deployer, limit, [], world}, accounts,
      _ => ok.init(deployer, limit, initial, world, accounts, c),
      _ => empty(deployer, limit, world, accounts)),
    _ => empty(deployer, limit, world, accounts))

def Laws.supply_sum(calls, accounts, deployer, limit, initial, world, e):
  keeps.trace(calls, Laws.deployed(deployer, limit, initial, world), accounts,
    keeps.init(deployer, limit, initial, world, accounts,
      once(deployer, accounts, N.and_left(Nat.is_eq(1n, Sum.count(deployer, accounts)), Laws.all_listed(calls, accounts), e))),
    N.and_right(Nat.is_eq(1n, Sum.count(deployer, accounts)), Laws.all_listed(calls, accounts), e))
