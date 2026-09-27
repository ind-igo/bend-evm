import Base
import ./Evm.bend as Evm
import ./nat.bend as N

# Sums over a mapping, for laws such as "the total is the sum of the
# balances": the values of a list of accounts in the mapping at a plain
# slot, and what a write of one account does to that sum.

def share(storage: List<&2, Evm.Slot>, +base: Nat, +a: Nat) -> Nat:
  Evm.lookup(storage, Evm.Mapped{Evm.Plain{base}, a})

def holdings(+storage: List<&2, Evm.Slot>, +base: Nat, accounts: List<&2, Nat>) -> Nat:
  match accounts:
    case Nil{}:
      0n
    case +a <> rest:
      Nat.add(share(storage, base, a), holdings(storage, base, rest))

def count(+who: Nat, accounts: List<&2, Nat>) -> Nat:
  match accounts:
    case Nil{}:
      0n
    case +a <> +rest:
      Bool.pick(Nat, Nat.is_eq(who, a), 1n+count(who, rest), count(who, rest))

# who's value after amount is added to it.
def credited(+storage: List<&2, Evm.Slot>, +base: Nat, +who: Nat, +amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{base}, who}, Nat.add(share(storage, base, who), amount)} <> storage

# who's value after amount is taken from it.
def debited(+storage: List<&2, Evm.Slot>, +base: Nat, +who: Nat, +amount: Nat) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{base}, who}, Nat.sub(share(storage, base, who), amount)} <> storage

def gain(+who: Nat, +amount: Nat, +a: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_eq(who, a), amount, 0n)

# amount once for each time who is in the list.
def hits(+who: Nat, +amount: Nat, accounts: List<&2, Nat>) -> Nat:
  match accounts:
    case Nil{}:
      0n
    case +a <> rest:
      Nat.add(gain(who, amount, a), hits(who, amount, rest))

def hits_count.go(+who: Nat, +amount: Nat, +a: Nat, +rest: List<&2, Nat>, +c: Bool, +ec: {c == Nat.is_eq(who, a) : Bool},
  +ih: {hits(who, amount, rest) == Nat.mul(count(who, rest), amount) : Nat}) ->
  {Nat.add(gain(who, amount, a), hits(who, amount, rest))
    == Nat.mul(Bool.pick(Nat, Nat.is_eq(who, a), 1n+count(who, rest), count(who, rest)), amount) : Nat}:
  match c:
    case True{}:
      %ec : {Nat.add(Bool.pick(Nat, _, amount, 0n), hits(who, amount, rest))
        == Nat.mul(Bool.pick(Nat, _, 1n+count(who, rest), count(who, rest)), amount) : Nat}
      %ih : {Nat.add(amount, hits(who, amount, rest)) == Nat.add(amount, _) : Nat}
      {==}
    case False{}:
      %ec : {Nat.add(Bool.pick(Nat, _, amount, 0n), hits(who, amount, rest))
        == Nat.mul(Bool.pick(Nat, _, 1n+count(who, rest), count(who, rest)), amount) : Nat}
      ih

def hits_count(+who: Nat, +amount: Nat, accounts: List<&2, Nat>) ->
  {hits(who, amount, accounts) == Nat.mul(count(who, accounts), amount) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      hits_count.go(who, amount, a, rest, Nat.is_eq(who, a), {==}, hits_count(who, amount, rest))

# An account that is in the list once gains the amount once.
def hits_once(+who: Nat, +amount: Nat, accounts: List<&2, Nat>, +e: {1n == count(who, accounts) : Nat}) ->
  {amount == hits(who, amount, accounts) : Nat}:
  %Equal.sym(Nat, hits(who, amount, accounts), Nat.mul(count(who, accounts), amount), hits_count(who, amount, accounts)) :
    {amount == _ : Nat}
  %e : {amount == Nat.mul(_, amount) : Nat}
  Equal.sym(Nat, Nat.add(amount, 0n), amount, N.add_zero(amount))

def credit_one(+storage: List<&2, Evm.Slot>, +base: Nat, +who: Nat, +amount: Nat, +a: Nat,
  +t: Bool, +et: {t == Nat.is_eq(who, a) : Bool}) ->
  {Nat.add(share(storage, base, a), gain(who, amount, a)) == share(credited(storage, base, who, amount), base, a) : Nat}:
  match t:
    case True{}:
      %N.eq_refl(base) : {Nat.add(share(storage, base, a), gain(who, amount, a))
        == Bool.pick(Nat, Bool.and(_, Nat.is_eq(who, a)), Nat.add(share(storage, base, who), amount), share(storage, base, a)) : Nat}
      %N.eq_sound(who, a, et) : {Nat.add(share(storage, base, _), gain(who, amount, _))
        == Bool.pick(Nat, Nat.is_eq(who, _), Nat.add(share(storage, base, who), amount), share(storage, base, _)) : Nat}
      %N.eq_refl(who) : {Nat.add(share(storage, base, who), Bool.pick(Nat, _, amount, 0n))
        == Bool.pick(Nat, _, Nat.add(share(storage, base, who), amount), share(storage, base, who)) : Nat}
      {==}
    case False{}:
      %N.eq_refl(base) : {Nat.add(share(storage, base, a), gain(who, amount, a))
        == Bool.pick(Nat, Bool.and(_, Nat.is_eq(who, a)), Nat.add(share(storage, base, who), amount), share(storage, base, a)) : Nat}
      %et : {Nat.add(share(storage, base, a), Bool.pick(Nat, _, amount, 0n))
        == Bool.pick(Nat, _, Nat.add(share(storage, base, who), amount), share(storage, base, a)) : Nat}
      N.add_zero(share(storage, base, a))

# A credit adds the amount once for each time who is listed.
def credit_sum(+storage: List<&2, Evm.Slot>, +base: Nat, +who: Nat, +amount: Nat, +accounts: List<&2, Nat>) ->
  {Nat.add(holdings(storage, base, accounts), hits(who, amount, accounts)) == holdings(credited(storage, base, who, amount), base, accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      %credit_one(storage, base, who, amount, a, Nat.is_eq(who, a), {==}) :
        {Nat.add(Nat.add(share(storage, base, a), holdings(storage, base, rest)), Nat.add(gain(who, amount, a), hits(who, amount, rest)))
          == Nat.add(_, holdings(credited(storage, base, who, amount), base, rest)) : Nat}
      %credit_sum(storage, base, who, amount, rest) :
        {Nat.add(Nat.add(share(storage, base, a), holdings(storage, base, rest)), Nat.add(gain(who, amount, a), hits(who, amount, rest)))
          == Nat.add(Nat.add(share(storage, base, a), gain(who, amount, a)), _) : Nat}
      N.swap4(share(storage, base, a), holdings(storage, base, rest), gain(who, amount, a), hits(who, amount, rest))

def debit_one(+storage: List<&2, Evm.Slot>, +base: Nat, +who: Nat, +amount: Nat, +a: Nat,
  +e: {False{} == Nat.is_lt(share(storage, base, who), amount) : Bool},
  +f: Bool, +ef: {f == Nat.is_eq(who, a) : Bool}) ->
  {Nat.add(share(debited(storage, base, who, amount), base, a), gain(who, amount, a)) == share(storage, base, a) : Nat}:
  match f:
    case True{}:
      %N.eq_refl(base) : {Nat.add(Bool.pick(Nat, Bool.and(_, Nat.is_eq(who, a)), Nat.sub(share(storage, base, who), amount),
        share(storage, base, a)), gain(who, amount, a)) == share(storage, base, a) : Nat}
      %N.eq_sound(who, a, ef) : {Nat.add(Bool.pick(Nat, Nat.is_eq(who, _), Nat.sub(share(storage, base, who), amount),
        share(storage, base, _)), gain(who, amount, _)) == share(storage, base, _) : Nat}
      %N.eq_refl(who) : {Nat.add(Bool.pick(Nat, _, Nat.sub(share(storage, base, who), amount), share(storage, base, who)),
        Bool.pick(Nat, _, amount, 0n)) == share(storage, base, who) : Nat}
      N.sub_add(share(storage, base, who), amount, e)
    case False{}:
      %N.eq_refl(base) : {Nat.add(Bool.pick(Nat, Bool.and(_, Nat.is_eq(who, a)), Nat.sub(share(storage, base, who), amount),
        share(storage, base, a)), gain(who, amount, a)) == share(storage, base, a) : Nat}
      %ef : {Nat.add(Bool.pick(Nat, _, Nat.sub(share(storage, base, who), amount), share(storage, base, a)),
        Bool.pick(Nat, _, amount, 0n)) == share(storage, base, a) : Nat}
      N.add_zero(share(storage, base, a))

# A debit that passes its check takes the amount once for each time who is
# listed.
def debit_sum(+storage: List<&2, Evm.Slot>, +base: Nat, +who: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +e: {False{} == Nat.is_lt(share(storage, base, who), amount) : Bool}) ->
  {Nat.add(holdings(debited(storage, base, who, amount), base, accounts), hits(who, amount, accounts)) == holdings(storage, base, accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      %Equal.sym(Nat, Nat.add(Nat.add(share(debited(storage, base, who, amount), base, a), holdings(debited(storage, base, who, amount), base, rest)), Nat.add(gain(who, amount, a), hits(who, amount, rest))),
        Nat.add(Nat.add(share(debited(storage, base, who, amount), base, a), gain(who, amount, a)), Nat.add(holdings(debited(storage, base, who, amount), base, rest), hits(who, amount, rest))),
        N.swap4(share(debited(storage, base, who, amount), base, a), holdings(debited(storage, base, who, amount), base, rest), gain(who, amount, a), hits(who, amount, rest))) :
        {_ == Nat.add(share(storage, base, a), holdings(storage, base, rest)) : Nat}
      %Equal.sym(Nat, Nat.add(share(debited(storage, base, who, amount), base, a), gain(who, amount, a)), share(storage, base, a),
        debit_one(storage, base, who, amount, a, e, Nat.is_eq(who, a), {==})) :
        {Nat.add(_, Nat.add(holdings(debited(storage, base, who, amount), base, rest), hits(who, amount, rest))) == Nat.add(share(storage, base, a), holdings(storage, base, rest)) : Nat}
      %Equal.sym(Nat, Nat.add(holdings(debited(storage, base, who, amount), base, rest), hits(who, amount, rest)), holdings(storage, base, rest),
        debit_sum(storage, base, who, amount, rest, e)) :
        {Nat.add(share(storage, base, a), _) == Nat.add(share(storage, base, a), holdings(storage, base, rest)) : Nat}
      {==}

# A credit of an account that is listed once adds the amount to the sum.
def credit_once(+storage: List<&2, Evm.Slot>, +base: Nat, +who: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +c: {1n == count(who, accounts) : Nat}) ->
  {Nat.add(holdings(storage, base, accounts), amount) == holdings(credited(storage, base, who, amount), base, accounts) : Nat}:
  %Equal.sym(Nat, amount, hits(who, amount, accounts), hits_once(who, amount, accounts, c)) :
    {Nat.add(holdings(storage, base, accounts), _) == holdings(credited(storage, base, who, amount), base, accounts) : Nat}
  credit_sum(storage, base, who, amount, accounts)

# A debit of an account that is listed once takes the amount from the sum.
def debit_once(+storage: List<&2, Evm.Slot>, +base: Nat, +who: Nat, +amount: Nat, +accounts: List<&2, Nat>,
  +e: {False{} == Nat.is_lt(share(storage, base, who), amount) : Bool}, +c: {1n == count(who, accounts) : Nat}) ->
  {Nat.add(holdings(debited(storage, base, who, amount), base, accounts), amount) == holdings(storage, base, accounts) : Nat}:
  %Equal.sym(Nat, amount, hits(who, amount, accounts), hits_once(who, amount, accounts, c)) :
    {Nat.add(holdings(debited(storage, base, who, amount), base, accounts), _) == holdings(storage, base, accounts) : Nat}
  debit_sum(storage, base, who, amount, accounts, e)

# A plain slot is not in the mapping.
def skip_plain(+storage: List<&2, Evm.Slot>, +base: Nat, +n: Nat, +v: Nat, +accounts: List<&2, Nat>) ->
  {holdings(storage, base, accounts) == holdings(Evm.Slot{Evm.Plain{n}, v} <> storage, base, accounts) : Nat}:
  match accounts:
    case Nil{}:
      {==}
    case +a <> +rest:
      %skip_plain(storage, base, n, v, rest) : {Nat.add(share(storage, base, a), holdings(storage, base, rest))
        == Nat.add(share(storage, base, a), _) : Nat}
      {==}
