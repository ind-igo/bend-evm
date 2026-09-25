import Base
import ../../../src/Evm.bend as Evm
import ./LAWS.bend as Laws

def Laws.keep(storage, who, limit, logs, world, x):
  Evm.branch.run(Nat, Nat.is_eq(x, 0n), Evm.Contract.pure(Nat, 0n),
    do Evm.Contract<Nat>:
      Evm.sstore(0n, x)
      Evm.Contract.pure(Nat, 1n), Evm.State{storage, who, limit, logs, world})

# The outer branch, then the inner one inside its second arm.
def Laws.grade(storage, who, limit, logs, world, x):
  +s = {Evm.State{storage, who, limit, logs, world} : Evm.State}
  -inner = Evm.branch(Nat, Nat.is_lt(x, 100n), Evm.Contract.pure(Nat, 1n), Evm.sub(x, 100n))
  Equal.trans(Evm.Outcome<Nat>, Evm.run(Nat, Evm.branch(Nat, Nat.is_lt(x, 10n), Evm.Contract.pure(Nat, 0n), inner), s),
    Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(x, 10n), Evm.Ok{0n, s}, Evm.run(Nat, inner, s)),
    Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(x, 10n), Evm.Ok{0n, s},
      Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(x, 100n), Evm.Ok{1n, s}, Evm.run(Nat, Evm.sub(x, 100n), s))),
    Evm.branch.run(Nat, Nat.is_lt(x, 10n), Evm.Contract.pure(Nat, 0n), inner, s),
    Equal.cong(Evm.Outcome<Nat>, Evm.Outcome<Nat>, m => Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(x, 10n), Evm.Ok{0n, s}, m),
      Evm.run(Nat, inner, s), Bool.pick(Evm.Outcome<Nat>, Nat.is_lt(x, 100n), Evm.Ok{1n, s}, Evm.run(Nat, Evm.sub(x, 100n), s)),
      Evm.branch.run(Nat, Nat.is_lt(x, 100n), Evm.Contract.pure(Nat, 1n), Evm.sub(x, 100n), s)))
