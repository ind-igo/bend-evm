import Base
import ../../src/Evm.bend as Evm
import ../../src/nat.bend as N
import ./LAWS.bend as Laws

def Laws.transfer(storage, from, limit, logs, world, to, amount):
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

def Laws.transferFrom(storage, who, limit, logs, world, from, to, amount):
  {==}

def Laws.init(storage, who, limit, logs, world, initial):
  {==}

def Laws.owner(storage, who, limit, logs, world):
  {==}

def Laws.transferOwnership(storage, who, limit, logs, world, next):
  {==}

# The supply law. Lemmas first: what one transfer or mint does to each
# balance, then to the sum over a list, then to the invariant.

def moved(+storage: List<&2, Evm.Slot>, +from: Nat, +to: Nat, +amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(Laws.balance(Laws.debit(storage, from, amount), to), amount)}
    <> Laws.debit(storage, from, amount)

def gain(+who: Nat, +amount: Nat, +a: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_eq(who, a), amount, 0n)

# The two sides of the per-account fact, with the comparisons as parameters.
def lhs(t: Bool, +f: Bool, v: Nat, d: Nat, b: Nat, +amount: Nat) -> Nat:
  Nat.add(Bool.pick(Nat, t, v, Bool.pick(Nat, f, d, b)), Bool.pick(Nat, f, amount, 0n))

def rhs(t: Bool, b: Nat, amount: Nat) -> Nat:
  Nat.add(b, Bool.pick(Nat, t, amount, 0n))

# The account `to` itself.
def at_to.go(+storage: List<&2, Evm.Slot>, +from: Nat, +to: Nat, +amount: Nat,
  +e: {False{} == Nat.is_lt(Laws.balance(storage, from), amount) : Bool},
  +f: Bool, +ef: {f == Nat.is_eq(from, to) : Bool}) ->
  {Nat.add(Nat.add(Bool.pick(Nat, Nat.is_eq(from, to), Nat.sub(Laws.balance(storage, from), amount), Laws.balance(storage, to)), amount),
    Bool.pick(Nat, Nat.is_eq(from, to), amount, 0n)) == Nat.add(Laws.balance(storage, to), amount) : Nat}:
  match f:
    case False{}:
      %ef : {Nat.add(Nat.add(Bool.pick(Nat, _, Nat.sub(Laws.balance(storage, from), amount), Laws.balance(storage, to)), amount),
        Bool.pick(Nat, _, amount, 0n)) == Nat.add(Laws.balance(storage, to), amount) : Nat}
      N.add_zero(Nat.add(Laws.balance(storage, to), amount))
    case True{}:
      %ef : {Nat.add(Nat.add(Bool.pick(Nat, _, Nat.sub(Laws.balance(storage, from), amount), Laws.balance(storage, to)), amount),
        Bool.pick(Nat, _, amount, 0n)) == Nat.add(Laws.balance(storage, to), amount) : Nat}
      %N.eq_sound(from, to, ef) : {Nat.add(Nat.add(Nat.sub(Laws.balance(storage, from), amount), amount), amount)
        == Nat.add(Laws.balance(storage, _), amount) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.sub(Laws.balance(storage, from), amount), amount), Laws.balance(storage, from),
        N.sub_add(Laws.balance(storage, from), amount, e)) :
        {Nat.add(_, amount) == Nat.add(Laws.balance(storage, from), amount) : Nat}
      {==}

def at_to(+storage: List<&2, Evm.Slot>, +from: Nat, +to: Nat, +amount: Nat,
  +e: {False{} == Nat.is_lt(Laws.balance(storage, from), amount) : Bool}) ->
  {Nat.add(Laws.balance(moved(storage, from, to, amount), to), gain(from, amount, to))
    == Nat.add(Laws.balance(storage, to), gain(to, amount, to)) : Nat}:
  %N.eq_refl(to) : {lhs(_, Nat.is_eq(from, to), Nat.add(Laws.balance(Laws.debit(storage, from, amount), to), amount),
    Nat.sub(Laws.balance(storage, from), amount), Laws.balance(storage, to), amount) == rhs(_, Laws.balance(storage, to), amount) : Nat}
  at_to.go(storage, from, to, amount, e, Nat.is_eq(from, to), {==})

# An account that is not `to`.
def off(+storage: List<&2, Evm.Slot>, +from: Nat, +amount: Nat, +a: Nat,
  +e: {False{} == Nat.is_lt(Laws.balance(storage, from), amount) : Bool},
  +f: Bool, +ef: {f == Nat.is_eq(from, a) : Bool}) ->
  {Nat.add(Bool.pick(Nat, Nat.is_eq(from, a), Nat.sub(Laws.balance(storage, from), amount), Laws.balance(storage, a)),
    Bool.pick(Nat, Nat.is_eq(from, a), amount, 0n)) == Nat.add(Laws.balance(storage, a), 0n) : Nat}:
  match f:
    case False{}:
      %ef : {Nat.add(Bool.pick(Nat, _, Nat.sub(Laws.balance(storage, from), amount), Laws.balance(storage, a)),
        Bool.pick(Nat, _, amount, 0n)) == Nat.add(Laws.balance(storage, a), 0n) : Nat}
      {==}
    case True{}:
      %ef : {Nat.add(Bool.pick(Nat, _, Nat.sub(Laws.balance(storage, from), amount), Laws.balance(storage, a)),
        Bool.pick(Nat, _, amount, 0n)) == Nat.add(Laws.balance(storage, a), 0n) : Nat}
      %N.eq_sound(from, a, ef) : {Nat.add(Nat.sub(Laws.balance(storage, from), amount), amount)
        == Nat.add(Laws.balance(storage, _), 0n) : Nat}
      %Equal.sym(Nat, Nat.add(Laws.balance(storage, from), 0n), Laws.balance(storage, from), N.add_zero(Laws.balance(storage, from))) :
        {Nat.add(Nat.sub(Laws.balance(storage, from), amount), amount) == _ : Nat}
      N.sub_add(Laws.balance(storage, from), amount, e)

def one.go(+storage: List<&2, Evm.Slot>, +from: Nat, +to: Nat, +amount: Nat, +a: Nat,
  +e: {False{} == Nat.is_lt(Laws.balance(storage, from), amount) : Bool},
  +t: Bool, +et: {t == Nat.is_eq(to, a) : Bool}) ->
  {Nat.add(Laws.balance(moved(storage, from, to, amount), a), gain(from, amount, a))
    == Nat.add(Laws.balance(storage, a), gain(to, amount, a)) : Nat}:
  match t:
    case True{}:
      %N.eq_sound(to, a, et) : {Nat.add(Laws.balance(moved(storage, from, to, amount), _), gain(from, amount, _))
        == Nat.add(Laws.balance(storage, _), gain(to, amount, _)) : Nat}
      at_to(storage, from, to, amount, e)
    case False{}:
      %et : {lhs(_, Nat.is_eq(from, a), Nat.add(Laws.balance(Laws.debit(storage, from, amount), to), amount),
        Nat.sub(Laws.balance(storage, from), amount), Laws.balance(storage, a), amount) == rhs(_, Laws.balance(storage, a), amount) : Nat}
      off(storage, from, amount, a, e, Nat.is_eq(from, a), {==})

# A transfer that passes its balance check moves amount from `from` to `to`.
def one(+storage: List<&2, Evm.Slot>, +from: Nat, +to: Nat, +amount: Nat, +a: Nat,
  +e: {False{} == Nat.is_lt(Laws.balance(storage, from), amount) : Bool}) ->
  {Nat.add(Laws.balance(moved(storage, from, to, amount), a), gain(from, amount, a))
    == Nat.add(Laws.balance(storage, a), gain(to, amount, a)) : Nat}:
  one.go(storage, from, to, amount, a, e, Nat.is_eq(to, a), {==})

def hits(+who: Nat, +amount: Nat, accounts: List<&2, Nat>) -> Nat:
  match accounts:
    case Nil{}:
      0n
    case +a <> rest:
      Nat.add(gain(who, amount, a), hits(who, amount, rest))

def sum_transfer(+storage: List<&2, Evm.Slot>, +from: Nat, +to: Nat, +amount: Nat, accounts: List<&2, Nat>,
  +e: {False{} == Nat.is_lt(Laws.balance(storage, from), amount) : Bool}) ->
  {Nat.add(Laws.holdings(moved(storage, from, to, amount), accounts), hits(from, amount, accounts))
    == Nat.add(Laws.holdings(storage, accounts), hits(to, amount, accounts)) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      %Equal.sym(Nat, Nat.add(Nat.add(Laws.balance(moved(storage, from, to, amount), a), Laws.holdings(moved(storage, from, to, amount), rest)),
          Nat.add(gain(from, amount, a), hits(from, amount, rest))),
        Nat.add(Nat.add(Laws.balance(moved(storage, from, to, amount), a), gain(from, amount, a)),
          Nat.add(Laws.holdings(moved(storage, from, to, amount), rest), hits(from, amount, rest))),
        N.swap4(Laws.balance(moved(storage, from, to, amount), a), Laws.holdings(moved(storage, from, to, amount), rest),
          gain(from, amount, a), hits(from, amount, rest))) :
        {_ == Nat.add(Nat.add(Laws.balance(storage, a), Laws.holdings(storage, rest)), Nat.add(gain(to, amount, a), hits(to, amount, rest))) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(Laws.balance(storage, a), Laws.holdings(storage, rest)), Nat.add(gain(to, amount, a), hits(to, amount, rest))),
        Nat.add(Nat.add(Laws.balance(storage, a), gain(to, amount, a)), Nat.add(Laws.holdings(storage, rest), hits(to, amount, rest))),
        N.swap4(Laws.balance(storage, a), Laws.holdings(storage, rest), gain(to, amount, a), hits(to, amount, rest))) :
        {Nat.add(Nat.add(Laws.balance(moved(storage, from, to, amount), a), gain(from, amount, a)),
          Nat.add(Laws.holdings(moved(storage, from, to, amount), rest), hits(from, amount, rest))) == _ : Nat}
      %one(storage, from, to, amount, a, e) :
        {Nat.add(Nat.add(Laws.balance(moved(storage, from, to, amount), a), gain(from, amount, a)),
          Nat.add(Laws.holdings(moved(storage, from, to, amount), rest), hits(from, amount, rest)))
          == Nat.add(_, Nat.add(Laws.holdings(storage, rest), hits(to, amount, rest))) : Nat}
      %sum_transfer(storage, from, to, amount, rest, e) :
        {Nat.add(Nat.add(Laws.balance(moved(storage, from, to, amount), a), gain(from, amount, a)),
          Nat.add(Laws.holdings(moved(storage, from, to, amount), rest), hits(from, amount, rest)))
          == Nat.add(Nat.add(Laws.balance(moved(storage, from, to, amount), a), gain(from, amount, a)), _) : Nat}
      {==}

def hits_count.go(+who: Nat, +amount: Nat, +a: Nat, +rest: List<&2, Nat>, +c: Bool, +ec: {c == Nat.is_eq(who, a) : Bool},
  +ih: {hits(who, amount, rest) == Nat.mul(Laws.count(who, rest), amount) : Nat}) ->
  {Nat.add(gain(who, amount, a), hits(who, amount, rest))
    == Nat.mul(Bool.pick(Nat, Nat.is_eq(who, a), 1n+Laws.count(who, rest), Laws.count(who, rest)), amount) : Nat}:
  match c:
    case True{}:
      %ec : {Nat.add(Bool.pick(Nat, _, amount, 0n), hits(who, amount, rest))
        == Nat.mul(Bool.pick(Nat, _, 1n+Laws.count(who, rest), Laws.count(who, rest)), amount) : Nat}
      %ih : {Nat.add(amount, hits(who, amount, rest)) == Nat.add(amount, _) : Nat}
      {==}
    case False{}:
      %ec : {Nat.add(Bool.pick(Nat, _, amount, 0n), hits(who, amount, rest))
        == Nat.mul(Bool.pick(Nat, _, 1n+Laws.count(who, rest), Laws.count(who, rest)), amount) : Nat}
      ih

def hits_count(+who: Nat, +amount: Nat, accounts: List<&2, Nat>) ->
  {hits(who, amount, accounts) == Nat.mul(Laws.count(who, accounts), amount) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      hits_count.go(who, amount, a, rest, Nat.is_eq(who, a), {==}, hits_count(who, amount, rest))

# An account that is in the list once gains the amount once.
def hits_once(+who: Nat, +amount: Nat, accounts: List<&2, Nat>, +e: {1n == Laws.count(who, accounts) : Nat}) ->
  {amount == hits(who, amount, accounts) : Nat}:
  %Equal.sym(Nat, hits(who, amount, accounts), Nat.mul(Laws.count(who, accounts), amount), hits_count(who, amount, accounts)) :
    {amount == _ : Nat}
  %e : {amount == Nat.mul(_, amount) : Nat}
  Equal.sym(Nat, Nat.add(amount, 0n), amount, N.add_zero(amount))

def keep_pick(-A: Data, +c: Bool, -a: Evm.Outcome<A>, -b: Evm.Outcome<A>, -s: Evm.State, -accounts: List<&2, Nat>,
  ha: {True{} == c : Bool} -> {True{} == Laws.balanced(Laws.after(A, a, s), accounts) : Bool},
  hb: {False{} == c : Bool} -> {True{} == Laws.balanced(Laws.after(A, b, s), accounts) : Bool}) ->
  {True{} == Laws.balanced(Laws.after(A, Bool.pick(Evm.Outcome<A>, c, a, b), s), accounts) : Bool}:
  match c:
    case True{}:
      ha({==})
    case False{}:
      hb({==})

def moved_sum(+storage: List<&2, Evm.Slot>, +from: Nat, +to: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +e: {False{} == Nat.is_lt(Laws.balance(storage, from), amount) : Bool},
  +cf: {1n == Laws.count(from, accounts) : Nat}, +ct: {1n == Laws.count(to, accounts) : Nat}) ->
  {Nat.add(Laws.holdings(moved(storage, from, to, amount), accounts), amount) == Nat.add(Laws.holdings(storage, accounts), amount) : Nat}:
  %Equal.sym(Nat, amount, hits(from, amount, accounts), hits_once(from, amount, accounts, cf)) :
    {Nat.add(Laws.holdings(moved(storage, from, to, amount), accounts), _) == Nat.add(Laws.holdings(storage, accounts), amount) : Nat}
  %Equal.sym(Nat, amount, hits(to, amount, accounts), hits_once(to, amount, accounts, ct)) :
    {Nat.add(Laws.holdings(moved(storage, from, to, amount), accounts), hits(from, amount, accounts))
      == Nat.add(Laws.holdings(storage, accounts), _) : Nat}
  sum_transfer(storage, from, to, amount, accounts, e)

# A transfer between two listed accounts keeps the listed holdings.
def holdings_moved(+storage: List<&2, Evm.Slot>, +from: Nat, +to: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +e: {False{} == Nat.is_lt(Laws.balance(storage, from), amount) : Bool},
  +cf: {1n == Laws.count(from, accounts) : Nat}, +ct: {1n == Laws.count(to, accounts) : Nat}) ->
  {Laws.holdings(storage, accounts) == Laws.holdings(moved(storage, from, to, amount), accounts) : Nat}:
  Equal.sym(Nat, Laws.holdings(moved(storage, from, to, amount), accounts), Laws.holdings(storage, accounts),
    N.cancel(Laws.holdings(moved(storage, from, to, amount), accounts), Laws.holdings(storage, accounts), amount,
      moved_sum(storage, from, to, amount, accounts, e, cf, ct)))

def ok.transfer(+storage: List<&2, Evm.Slot>, +who: Nat, +to: Nat, +amount: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  -s: Evm.State, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool},
  +e: {False{} == Nat.is_lt(Laws.balance(storage, who), amount) : Bool},
  +cf: {1n == Laws.count(who, accounts) : Nat}, +ct: {1n == Laws.count(to, accounts) : Nat}) ->
  {True{} == Laws.balanced(Laws.after(Nat, Evm.Ok{1n, Evm.State{moved(storage, who, to, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [who, to], [amount]} <> logs, world}}, s), accounts) : Bool}:
  %holdings_moved(storage, who, to, amount, accounts, e, cf, ct) : {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

def keeps.transfer(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +to: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool},
  +cf: {1n == Laws.count(who, accounts) : Nat}, +ct: {1n == Laws.count(to, accounts) : Nat}) ->
  {True{} == Laws.balanced(Laws.step(Laws.Tx{world, Laws.Transfer{who, to, amount}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  keep_pick(Nat, Nat.is_lt(Laws.balance(storage, who), amount), Evm.Revert{},
    Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(Nat.add(Laws.balance(Laws.debit(storage, who, amount), to), amount), limit),
      Evm.Ok{1n, Evm.State{moved(storage, who, to, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [who, to], [amount]} <> logs, world}}, Evm.Revert{}),
    Evm.State{storage, caller, limit, logs, old}, accounts,
    _ => h,
    e => keep_pick(Nat, Nat.is_lt(Nat.add(Laws.balance(Laws.debit(storage, who, amount), to), amount), limit),
      Evm.Ok{1n, Evm.State{moved(storage, who, to, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [who, to], [amount]} <> logs, world}}, Evm.Revert{},
      Evm.State{storage, caller, limit, logs, old}, accounts,
      _ => ok.transfer(storage, who, to, amount, limit, logs, world, Evm.State{storage, caller, limit, logs, old}, accounts, h, e, cf, ct),
      _ => h))

def minted(+storage: List<&2, Evm.Slot>, +to: Nat, +amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{1n}, to}, Nat.add(Laws.balance(storage, to), amount)}
    <> Evm.Slot{Evm.Plain{0n}, Nat.add(Laws.supply(storage), amount)} <> storage

def mint_one.go(+storage: List<&2, Evm.Slot>, +to: Nat, +amount: Nat, +a: Nat, +t: Bool, +et: {t == Nat.is_eq(to, a) : Bool}) ->
  {Nat.add(Laws.balance(storage, a), gain(to, amount, a)) == Laws.balance(minted(storage, to, amount), a) : Nat}:
  match t:
    case True{}:
      %N.eq_sound(to, a, et) : {Nat.add(Laws.balance(storage, _), gain(to, amount, _)) == Laws.balance(minted(storage, to, amount), _) : Nat}
      %N.eq_refl(to) : {Nat.add(Laws.balance(storage, to), Bool.pick(Nat, _, amount, 0n))
        == Bool.pick(Nat, _, Nat.add(Laws.balance(storage, to), amount), Laws.balance(storage, to)) : Nat}
      {==}
    case False{}:
      %et : {Nat.add(Laws.balance(storage, a), Bool.pick(Nat, _, amount, 0n))
        == Bool.pick(Nat, _, Nat.add(Laws.balance(storage, to), amount), Laws.balance(storage, a)) : Nat}
      N.add_zero(Laws.balance(storage, a))

def mint_sum(+storage: List<&2, Evm.Slot>, +to: Nat, +amount: Nat, +accounts: List<&2, Nat>) ->
  {Nat.add(Laws.holdings(storage, accounts), hits(to, amount, accounts)) == Laws.holdings(minted(storage, to, amount), accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      %mint_one.go(storage, to, amount, a, Nat.is_eq(to, a), {==}) :
        {Nat.add(Nat.add(Laws.balance(storage, a), Laws.holdings(storage, rest)), Nat.add(gain(to, amount, a), hits(to, amount, rest)))
          == Nat.add(_, Laws.holdings(minted(storage, to, amount), rest)) : Nat}
      %mint_sum(storage, to, amount, rest) :
        {Nat.add(Nat.add(Laws.balance(storage, a), Laws.holdings(storage, rest)), Nat.add(gain(to, amount, a), hits(to, amount, rest)))
          == Nat.add(Nat.add(Laws.balance(storage, a), gain(to, amount, a)), _) : Nat}
      N.swap4(Laws.balance(storage, a), Laws.holdings(storage, rest), gain(to, amount, a), hits(to, amount, rest))

# A slot of a nested mapping, such as an allowance, is not a balance.
def skip_nested(+storage: List<&2, Evm.Slot>, +k: Evm.Key, +x: Nat, +y: Nat, +v: Nat, +accounts: List<&2, Nat>) ->
  {Laws.holdings(storage, accounts) == Laws.holdings(Evm.Slot{Evm.Mapped{Evm.Mapped{k, x}, y}, v} <> storage, accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      %skip_nested(storage, k, x, y, v, rest) : {Nat.add(Laws.balance(storage, a), Laws.holdings(storage, rest))
        == Nat.add(Laws.balance(storage, a), _) : Nat}
      {==}

# Nor is a plain slot.
def skip_plain(+storage: List<&2, Evm.Slot>, +n: Nat, +v: Nat, +accounts: List<&2, Nat>) ->
  {Laws.holdings(storage, accounts) == Laws.holdings(Evm.Slot{Evm.Plain{n}, v} <> storage, accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      %skip_plain(storage, n, v, rest) : {Nat.add(Laws.balance(storage, a), Laws.holdings(storage, rest))
        == Nat.add(Laws.balance(storage, a), _) : Nat}
      {==}

def ok.mint(+storage: List<&2, Evm.Slot>, +who: Nat, +to: Nat, +amount: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  -s: Evm.State, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool},
  +ct: {1n == Laws.count(to, accounts) : Nat}) ->
  {True{} == Laws.balanced(Laws.after(Unit, Evm.Ok{Unit{}, Evm.State{minted(storage, to, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [0n, to], [amount]} <> logs, world}}, s), accounts) : Bool}:
  %mint_sum(storage, to, amount, accounts) : {True{} == Nat.is_eq(Nat.add(Laws.supply(storage), amount), _) : Bool}
  %hits_once(to, amount, accounts, ct) :
    {True{} == Nat.is_eq(Nat.add(Laws.supply(storage), amount), Nat.add(Laws.holdings(storage, accounts), _)) : Bool}
  %N.eq_sound(Laws.supply(storage), Laws.holdings(storage, accounts), h) :
    {True{} == Nat.is_eq(Nat.add(Laws.supply(storage), amount), Nat.add(_, amount)) : Bool}
  N.eq_refl(Nat.add(Laws.supply(storage), amount))

def keeps.mint(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +to: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool},
  +ct: {1n == Laws.count(to, accounts) : Nat}) ->
  {True{} == Laws.balanced(Laws.step(Laws.Tx{world, Laws.Mint{who, to, amount}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  keep_pick(Unit, Nat.is_eq(who, Evm.lookup(storage, Evm.Plain{4n})),
    Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.supply(storage), amount), limit),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.balance(storage, to), amount), limit),
        Evm.Ok{Unit{}, Evm.State{minted(storage, to, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [0n, to], [amount]} <> logs, world}}, Evm.Revert{}),
      Evm.Revert{}),
    Evm.Revert{}, Evm.State{storage, caller, limit, logs, old}, accounts,
    _ => keep_pick(Unit, Nat.is_lt(Nat.add(Laws.supply(storage), amount), limit),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.balance(storage, to), amount), limit),
        Evm.Ok{Unit{}, Evm.State{minted(storage, to, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [0n, to], [amount]} <> logs, world}}, Evm.Revert{}),
      Evm.Revert{}, Evm.State{storage, caller, limit, logs, old}, accounts,
      _ => keep_pick(Unit, Nat.is_lt(Nat.add(Laws.balance(storage, to), amount), limit),
        Evm.Ok{Unit{}, Evm.State{minted(storage, to, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [0n, to], [amount]} <> logs, world}}, Evm.Revert{},
        Evm.State{storage, caller, limit, logs, old}, accounts,
        _ => ok.mint(storage, who, to, amount, limit, logs, world, Evm.State{storage, caller, limit, logs, old}, accounts, h, ct),
        _ => h),
      _ => h),
    _ => h)

def keeps.approve(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +spender: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool}) ->
  {True{} == Laws.balanced(Laws.step(Laws.Tx{world, Laws.Approve{who, spender, amount}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  %skip_nested(storage, Evm.Plain{2n}, who, spender, amount, accounts) : {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

def ok.owner(+storage: List<&2, Evm.Slot>, +next: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool}) ->
  {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(Evm.Slot{Evm.Plain{4n}, next} <> storage, accounts)) : Bool}:
  %skip_plain(storage, 4n, next, accounts) : {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

def keeps.transferOwnership(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +next: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool}) ->
  {True{} == Laws.balanced(Laws.step(Laws.Tx{world, Laws.TransferOwnership{who, next}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  keep_pick(Unit, Nat.is_eq(who, Evm.lookup(storage, Evm.Plain{4n})),
    Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{4n}, next} <> storage, who, limit, Evm.Log{"OwnershipTransferred(address,address)", [Evm.lookup(storage, Evm.Plain{4n}), next], []} <> logs, world}},
    Evm.Revert{}, Evm.State{storage, caller, limit, logs, old}, accounts,
    _ => ok.owner(storage, next, accounts, h),
    _ => h)

# The storage after transferFrom lowers the allowance.
def lowered(+storage: List<&2, Evm.Slot>, +holder: Nat, +spender: Nat, +limit: Nat, +amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Mapped{Evm.Plain{2n}, holder}, spender},
    Nat.sub(Laws.allowed(storage, holder, spender), Laws.spent(storage, holder, spender, limit, amount))} <> storage

def ok.transferFrom(+storage: List<&2, Evm.Slot>, +who: Nat, +from: Nat, +to: Nat, +amount: Nat, +limit: Nat,
  +logs: List<&2, Evm.Log>, +world: Evm.World, -s: Evm.State, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool},
  +e: {False{} == Nat.is_lt(Laws.balance(lowered(storage, from, who, limit, amount), from), amount) : Bool},
  +cf: {1n == Laws.count(from, accounts) : Nat}, +ct: {1n == Laws.count(to, accounts) : Nat}) ->
  {True{} == Laws.balanced(Laws.after(Nat, Evm.Ok{1n, Evm.State{moved(lowered(storage, from, who, limit, amount), from, to, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [from, to], [amount]} <> logs, world}}, s), accounts) : Bool}:
  %holdings_moved(lowered(storage, from, who, limit, amount), from, to, amount, accounts, e, cf, ct) :
    {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  %skip_nested(storage, Evm.Plain{2n}, from, who,
    Nat.sub(Laws.allowed(storage, from, who), Laws.spent(storage, from, who, limit, amount)), accounts) :
    {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

def keeps.transferFrom(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +from: Nat, +to: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool},
  +cf: {1n == Laws.count(from, accounts) : Nat}, +ct: {1n == Laws.count(to, accounts) : Nat}) ->
  {True{} == Laws.balanced(Laws.step(Laws.Tx{world, Laws.TransferFrom{who, from, to, amount}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  keep_pick(Nat, Nat.is_lt(Laws.allowed(storage, from, who), Laws.spent(storage, from, who, limit, amount)), Evm.Revert{},
    Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(Laws.balance(lowered(storage, from, who, limit, amount), from), amount), Evm.Revert{},
      Bool.pick(Evm.Outcome<Nat>,
        Nat.is_lt(Nat.add(Laws.balance(Laws.debit(lowered(storage, from, who, limit, amount), from, amount), to), amount), limit),
        Evm.Ok{1n, Evm.State{moved(lowered(storage, from, who, limit, amount), from, to, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [from, to], [amount]} <> logs, world}}, Evm.Revert{})),
    Evm.State{storage, caller, limit, logs, old}, accounts,
    _ => h,
    _ => keep_pick(Nat, Nat.is_lt(Laws.balance(lowered(storage, from, who, limit, amount), from), amount), Evm.Revert{},
      Bool.pick(Evm.Outcome<Nat>,
        Nat.is_lt(Nat.add(Laws.balance(Laws.debit(lowered(storage, from, who, limit, amount), from, amount), to), amount), limit),
        Evm.Ok{1n, Evm.State{moved(lowered(storage, from, who, limit, amount), from, to, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [from, to], [amount]} <> logs, world}}, Evm.Revert{}),
      Evm.State{storage, caller, limit, logs, old}, accounts,
      _ => h,
      e => keep_pick(Nat,
        Nat.is_lt(Nat.add(Laws.balance(Laws.debit(lowered(storage, from, who, limit, amount), from, amount), to), amount), limit),
        Evm.Ok{1n, Evm.State{moved(lowered(storage, from, who, limit, amount), from, to, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [from, to], [amount]} <> logs, world}}, Evm.Revert{},
        Evm.State{storage, caller, limit, logs, old}, accounts,
        _ => ok.transferFrom(storage, who, from, to, amount, limit, logs, world, Evm.State{storage, caller, limit, logs, old}, accounts,
          h, e, cf, ct),
        _ => h)))

# A burn debits the caller: the listed holdings fall by the amount.
def burn_sum(+storage: List<&2, Evm.Slot>, +who: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +e: {False{} == Nat.is_lt(Laws.balance(storage, who), amount) : Bool}) ->
  {Nat.add(Laws.holdings(Laws.debit(storage, who, amount), accounts), hits(who, amount, accounts)) == Laws.holdings(storage, accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      %Equal.sym(Nat, Nat.add(Nat.add(Laws.balance(Laws.debit(storage, who, amount), a), Laws.holdings(Laws.debit(storage, who, amount), rest)),
          Nat.add(gain(who, amount, a), hits(who, amount, rest))),
        Nat.add(Nat.add(Laws.balance(Laws.debit(storage, who, amount), a), gain(who, amount, a)),
          Nat.add(Laws.holdings(Laws.debit(storage, who, amount), rest), hits(who, amount, rest))),
        N.swap4(Laws.balance(Laws.debit(storage, who, amount), a), Laws.holdings(Laws.debit(storage, who, amount), rest),
          gain(who, amount, a), hits(who, amount, rest))) :
        {_ == Nat.add(Laws.balance(storage, a), Laws.holdings(storage, rest)) : Nat}
      %Equal.trans(Nat, Laws.balance(storage, a), Nat.add(Laws.balance(storage, a), 0n),
        Nat.add(Laws.balance(Laws.debit(storage, who, amount), a), gain(who, amount, a)),
        Equal.sym(Nat, Nat.add(Laws.balance(storage, a), 0n), Laws.balance(storage, a), N.add_zero(Laws.balance(storage, a))),
        Equal.sym(Nat, Nat.add(Laws.balance(Laws.debit(storage, who, amount), a), gain(who, amount, a)), Nat.add(Laws.balance(storage, a), 0n),
          off(storage, who, amount, a, e, Nat.is_eq(who, a), {==}))) :
        {Nat.add(_, Nat.add(Laws.holdings(Laws.debit(storage, who, amount), rest), hits(who, amount, rest)))
          == Nat.add(Laws.balance(storage, a), Laws.holdings(storage, rest)) : Nat}
      %burn_sum(storage, who, amount, rest, e) :
        {Nat.add(Laws.balance(storage, a), Nat.add(Laws.holdings(Laws.debit(storage, who, amount), rest), hits(who, amount, rest)))
          == Nat.add(Laws.balance(storage, a), _) : Nat}
      {==}

def burn_total(+storage: List<&2, Evm.Slot>, +who: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +e: {False{} == Nat.is_lt(Laws.balance(storage, who), amount) : Bool}, +c: {1n == Laws.count(who, accounts) : Nat}) ->
  {Nat.add(Laws.holdings(Laws.debit(storage, who, amount), accounts), amount) == Laws.holdings(storage, accounts) : Nat}:
  %Equal.sym(Nat, amount, hits(who, amount, accounts), hits_once(who, amount, accounts, c)) :
    {Nat.add(Laws.holdings(Laws.debit(storage, who, amount), accounts), _) == Laws.holdings(storage, accounts) : Nat}
  burn_sum(storage, who, amount, accounts, e)

def ok.burn(+storage: List<&2, Evm.Slot>, +who: Nat, +amount: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  -s: Evm.State, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool},
  +e: {False{} == Nat.is_lt(Laws.balance(storage, who), amount) : Bool}, +c: {1n == Laws.count(who, accounts) : Nat}) ->
  {True{} == Laws.balanced(Laws.after(Unit, Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{0n}, Nat.sub(Laws.supply(storage), amount)}
    <> Laws.debit(storage, who, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [who, 0n], [amount]} <> logs, world}}, s),
    accounts) : Bool}:
  %skip_plain(Laws.debit(storage, who, amount), 0n, Nat.sub(Laws.supply(storage), amount), accounts) :
    {True{} == Nat.is_eq(Nat.sub(Laws.supply(storage), amount), _) : Bool}
  %Equal.sym(Nat, Laws.supply(storage), Laws.holdings(storage, accounts),
    N.eq_sound(Laws.supply(storage), Laws.holdings(storage, accounts), h)) :
    {True{} == Nat.is_eq(Nat.sub(_, amount), Laws.holdings(Laws.debit(storage, who, amount), accounts)) : Bool}
  %burn_total(storage, who, amount, accounts, e, c) :
    {True{} == Nat.is_eq(Nat.sub(_, amount), Laws.holdings(Laws.debit(storage, who, amount), accounts)) : Bool}
  %N.add_comm(amount, Laws.holdings(Laws.debit(storage, who, amount), accounts)) :
    {True{} == Nat.is_eq(Nat.sub(_, amount), Laws.holdings(Laws.debit(storage, who, amount), accounts)) : Bool}
  %N.sub_add_cancel(Laws.holdings(Laws.debit(storage, who, amount), accounts), amount) :
    {True{} == Nat.is_eq(_, Laws.holdings(Laws.debit(storage, who, amount), accounts)) : Bool}
  N.eq_refl(Laws.holdings(Laws.debit(storage, who, amount), accounts))

def keeps.burn(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World, +world: Evm.World,
  +who: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool},
  +c: {1n == Laws.count(who, accounts) : Nat}) ->
  {True{} == Laws.balanced(Laws.step(Laws.Tx{world, Laws.Burn{who, amount}}, Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  keep_pick(Unit, Nat.is_lt(Laws.balance(storage, who), amount), Evm.Revert{},
    Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Laws.supply(storage), amount), Evm.Revert{},
      Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{0n}, Nat.sub(Laws.supply(storage), amount)} <> Laws.debit(storage, who, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [who, 0n], [amount]} <> logs, world}}),
    Evm.State{storage, caller, limit, logs, old}, accounts,
    _ => h,
    e => keep_pick(Unit, Nat.is_lt(Laws.supply(storage), amount), Evm.Revert{},
      Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{0n}, Nat.sub(Laws.supply(storage), amount)} <> Laws.debit(storage, who, amount), who, limit, Evm.Log{"Transfer(address,address,uint256)", [who, 0n], [amount]} <> logs, world}},
      Evm.State{storage, caller, limit, logs, old}, accounts,
      _ => h,
      _ => ok.burn(storage, who, amount, limit, logs, world, Evm.State{storage, caller, limit, logs, old}, accounts, h, e, c)))

# A nonce is not a balance either.
def skip_nonce(+storage: List<&2, Evm.Slot>, +o: Nat, +v: Nat, +accounts: List<&2, Nat>) ->
  {Laws.holdings(storage, accounts) == Laws.holdings(Evm.Slot{Evm.Mapped{Evm.Plain{3n}, o}, v} <> storage, accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      %skip_nonce(storage, o, v, rest) : {Nat.add(Laws.balance(storage, a), Laws.holdings(storage, rest))
        == Nat.add(Laws.balance(storage, a), _) : Nat}
      {==}

def permitted(+storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  +owner: Nat, +spender: Nat, +value: Nat) -> Evm.Outcome<Unit>:
  Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Mapped{Evm.Mapped{Evm.Plain{2n}, owner}, spender}, value}
    <> Evm.Slot{Evm.Mapped{Evm.Plain{3n}, owner}, Nat.add(Laws.nonce(storage, owner), 1n)} <> storage, who, limit,
    Evm.Log{"Approval(address,address,uint256)", [owner, spender], [value]} <> logs, world}}

def ok.permit(+storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  +owner: Nat, +spender: Nat, +value: Nat, -s: Evm.State, +accounts: List<&2, Nat>,
  +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool}) ->
  {True{} == Laws.balanced(Laws.after(Unit, permitted(storage, who, limit, logs, world, owner, spender, value), s), accounts) : Bool}:
  %skip_nested(Evm.Slot{Evm.Mapped{Evm.Plain{3n}, owner}, Nat.add(Laws.nonce(storage, owner), 1n)} <> storage, Evm.Plain{2n},
    owner, spender, value, accounts) : {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  %skip_nonce(storage, owner, Nat.add(Laws.nonce(storage, owner), 1n), accounts) :
    {True{} == Nat.is_eq(Laws.supply(storage), _) : Bool}
  h

def keeps.permit(+storage: List<&2, Evm.Slot>, +caller: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +old: Evm.World,
  +world: Evm.World, +who: Nat, +owner: Nat, +spender: Nat, +value: Nat, +deadline: Nat, +v: Nat, +r: Nat, +sig: Nat,
  +accounts: List<&2, Nat>, +h: {True{} == Nat.is_eq(Laws.supply(storage), Laws.holdings(storage, accounts)) : Bool}) ->
  {True{} == Laws.balanced(Laws.step(Laws.Tx{world, Laws.Permit{who, owner, spender, value, deadline, v, r, sig}},
    Evm.State{storage, caller, limit, logs, old}), accounts) : Bool}:
  +signer = Laws.permitter(world, storage, owner, spender, value, deadline, v, r, sig)
  +ok = permitted(storage, who, limit, logs, world, owner, spender, value)
  +before = {Evm.State{storage, caller, limit, logs, old} : Evm.State}
  +d = Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(signer, owner), ok, Evm.Revert{})
  +c = Bool.pick(Evm.Outcome<Unit>, Bool.not(Nat.is_eq(signer, 0n)), d, Evm.Revert{})
  +b = Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.nonce(storage, owner), 1n), limit), c, Evm.Revert{})
  keep_pick(Unit, Bool.not(Nat.is_lt(deadline, Evm.time.of(world))), b, Evm.Revert{}, before, accounts,
    _ => keep_pick(Unit, Nat.is_lt(Nat.add(Laws.nonce(storage, owner), 1n), limit), c, Evm.Revert{}, before, accounts,
      _ => keep_pick(Unit, Bool.not(Nat.is_eq(signer, 0n)), d, Evm.Revert{}, before, accounts,
        _ => keep_pick(Unit, Nat.is_eq(signer, owner), ok, Evm.Revert{}, before, accounts,
          _ => ok.permit(storage, who, limit, logs, world, owner, spender, value, before, accounts, h),
          _ => h),
        _ => h),
      _ => h),
    _ => h)

def and_left(+x: Bool, +y: Bool, +e: {True{} == Bool.and(x, y) : Bool}) -> {True{} == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      e

def and_right(+x: Bool, +y: Bool, +e: {True{} == Bool.and(x, y) : Bool}) -> {True{} == y : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      N.absurd({True{} == y : Bool}, e)

def once(+who: Nat, +accounts: List<&2, Nat>, +e: {True{} == Nat.is_eq(1n, Laws.count(who, accounts)) : Bool}) ->
  {1n == Laws.count(who, accounts) : Nat}:
  N.eq_sound(1n, Laws.count(who, accounts), e)

def keeps.step(+t: Laws.Tx, +s: Evm.State, +accounts: List<&2, Nat>, +h: {True{} == Laws.balanced(s, accounts) : Bool},
  +l: {True{} == Laws.listed.tx(t, accounts) : Bool}) -> {True{} == Laws.balanced(Laws.step(t, s), accounts) : Bool}:
  match t s:
    case Laws.Tx{+world, Laws.Transfer{+who, +to, +amount}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.transfer(storage, caller, limit, logs, old, world, who, to, amount, accounts, h,
        once(who, accounts, and_left(Nat.is_eq(1n, Laws.count(who, accounts)), Nat.is_eq(1n, Laws.count(to, accounts)), l)),
        once(to, accounts, and_right(Nat.is_eq(1n, Laws.count(who, accounts)), Nat.is_eq(1n, Laws.count(to, accounts)), l)))
    case Laws.Tx{+world, Laws.Mint{+who, +to, +amount}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.mint(storage, caller, limit, logs, old, world, who, to, amount, accounts, h, once(to, accounts, l))
    case Laws.Tx{+world, Laws.Approve{+who, +spender, +amount}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.approve(storage, caller, limit, logs, old, world, who, spender, amount, accounts, h)
    case Laws.Tx{+world, Laws.TransferFrom{+who, +from, +to, +amount}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.transferFrom(storage, caller, limit, logs, old, world, who, from, to, amount, accounts, h,
        once(from, accounts, and_left(Nat.is_eq(1n, Laws.count(from, accounts)), Nat.is_eq(1n, Laws.count(to, accounts)), l)),
        once(to, accounts, and_right(Nat.is_eq(1n, Laws.count(from, accounts)), Nat.is_eq(1n, Laws.count(to, accounts)), l)))
    case Laws.Tx{+world, Laws.TransferOwnership{+who, +next}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.transferOwnership(storage, caller, limit, logs, old, world, who, next, accounts, h)
    case Laws.Tx{+world, Laws.Permit{+who, +owner, +spender, +value, +deadline, +v, +r, +sig}}
      Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.permit(storage, caller, limit, logs, old, world, who, owner, spender, value, deadline, v, r, sig, accounts, h)
    case Laws.Tx{+world, Laws.Burn{+who, +amount}} Evm.State{+storage, +caller, +limit, +logs, +old}:
      keeps.burn(storage, caller, limit, logs, old, world, who, amount, accounts, h, once(who, accounts, l))

def keeps.trace(+calls: List<&2, Laws.Tx>, +s: Evm.State, +accounts: List<&2, Nat>, +h: {True{} == Laws.balanced(s, accounts) : Bool},
  +l: {True{} == Laws.all_listed(calls, accounts) : Bool}) -> {True{} == Laws.balanced(Laws.trace(calls, s), accounts) : Bool}:
  match calls:
    case Nil{}:
      h
    case +c <> +rest:
      keeps.trace(rest, Laws.step(c, s), accounts,
        keeps.step(c, s, accounts, h, and_left(Laws.listed.tx(c, accounts), Laws.all_listed(rest, accounts), l)),
        and_right(Laws.listed.tx(c, accounts), Laws.all_listed(rest, accounts), l))

def init_sum(+deployer: Nat, +initial: Nat, +accounts: List<&2, Nat>) ->
  {hits(deployer, initial, accounts) == Laws.holdings(Evm.Slot{Evm.Mapped{Evm.Plain{1n}, deployer}, initial}
    <> Evm.Slot{Evm.Plain{0n}, initial} <> Evm.Slot{Evm.Plain{4n}, deployer} <> [], accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      %init_sum(deployer, initial, rest) : {Nat.add(gain(deployer, initial, a), hits(deployer, initial, rest))
        == Nat.add(gain(deployer, initial, a), _) : Nat}
      {==}

def init_storage(+deployer: Nat, +initial: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{1n}, deployer}, initial} <> Evm.Slot{Evm.Plain{0n}, initial}
    <> Evm.Slot{Evm.Plain{4n}, deployer} <> []

def init_ok(+deployer: Nat, +limit: Nat, +initial: Nat, +world: Evm.World) -> Evm.Outcome<Unit>:
  Evm.Ok{Unit{}, Evm.State{init_storage(deployer, initial), deployer, limit, [Evm.Log{"Transfer(address,address,uint256)", [0n, deployer], [initial]},
      Evm.Log{"OwnershipTransferred(address,address)", [0n, deployer], []}], world}}

def ok.init(+deployer: Nat, +limit: Nat, +initial: Nat, +world: Evm.World, +accounts: List<&2, Nat>,
  +c: {1n == Laws.count(deployer, accounts) : Nat}) ->
  {True{} == Laws.balanced(Laws.after(Unit, init_ok(deployer, limit, initial, world), Evm.State{[], deployer, limit, [], world}), accounts) : Bool}:
  %init_sum(deployer, initial, accounts) : {True{} == Nat.is_eq(initial, _) : Bool}
  %hits_once(deployer, initial, accounts, c) : {True{} == Nat.is_eq(initial, _) : Bool}
  N.eq_refl(initial)

# No account holds anything in empty storage.
def holdings_empty(+accounts: List<&2, Nat>) -> {0n == Laws.holdings([], accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      holdings_empty(rest)

def empty(+deployer: Nat, +limit: Nat, +world: Evm.World, +accounts: List<&2, Nat>) ->
  {True{} == Laws.balanced(Evm.State{[], deployer, limit, [], world}, accounts) : Bool}:
  %holdings_empty(accounts) : {True{} == Nat.is_eq(0n, _) : Bool}
  {==}

# Deployment mints the initial supply to the deployer, or reverts.
def keeps.init(+deployer: Nat, +limit: Nat, +initial: Nat, +world: Evm.World, +accounts: List<&2, Nat>,
  +c: {1n == Laws.count(deployer, accounts) : Nat}) -> {True{} == Laws.balanced(Laws.deployed(deployer, limit, initial, world), accounts) : Bool}:
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
      once(deployer, accounts, and_left(Nat.is_eq(1n, Laws.count(deployer, accounts)), Laws.all_listed(calls, accounts), e))),
    and_right(Nat.is_eq(1n, Laws.count(deployer, accounts)), Laws.all_listed(calls, accounts), e))
