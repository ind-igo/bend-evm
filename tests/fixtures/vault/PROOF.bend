import Base
import ../../../src/Evm.bend as Evm
import ../../../src/calls.bend as Calls
import ./program.bend as Program
import ./CERT.bend as Cert
import ./LAWS.bend as Laws

# The checks before the call are picks that the run cannot pass until the
# hypotheses decide them.

def paying(+storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  +amount: Nat) -> Evm.Outcome<Unit>:
  Evm.Calling{Evm.Call{Laws.token(storage), "transfer", [who, amount]},
    Laws.moved(storage, who, limit, logs, world, Nat.sub(Laws.shares(storage, who), amount), Nat.sub(Laws.total(storage), amount)),
    x => t => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n), Evm.Ok{Unit{}, t}, Evm.Revert{})}

def taking(+storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  +amount: Nat) -> Evm.Outcome<Unit>:
  Evm.Calling{Evm.Call{Laws.token(storage), "transferFrom", [who, Evm.self.of(world), amount]},
    Laws.moved(storage, who, limit, logs, world, Nat.add(Laws.shares(storage, who), amount), Nat.add(Laws.total(storage), amount)),
    x => t => Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(x, 1n), Evm.Ok{Unit{}, t}, Evm.Revert{})}

def Laws.withdraw(storage, who, limit, logs, world, q, amount, e1, e2):
  -steps = {[Calls.Answer{q, [], 1n}] : List<&2, Calls.Step>}
  -rhs = {Bool.pick(Evm.Outcome<Unit>, Evm.same.call(q, Evm.Call{Laws.token(storage), "transfer", [who, amount]}),
      Evm.Ok{Unit{}, Laws.moved(storage, who, limit, logs, world, Nat.sub(Laws.shares(storage, who), amount), Nat.sub(Laws.total(storage), amount))},
      Evm.Revert{}) : Evm.Outcome<Unit>}
  %e1 : {Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, False{}, Bool.pick(Evm.Outcome<Unit>, _, Evm.Revert{},
    Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Laws.total(storage), amount), Evm.Revert{}, paying(storage, who, limit, logs, world, amount))))
    == rhs : Evm.Outcome<Unit>}
  %e2 : {Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, False{},
    Bool.pick(Evm.Outcome<Unit>, _, Evm.Revert{}, paying(storage, who, limit, logs, world, amount))) == rhs : Evm.Outcome<Unit>}
  {==}

def Laws.deposit(storage, who, limit, logs, world, q, cbs, amount, e1, e2):
  -steps = {[Calls.Answer{q, cbs, 1n}] : List<&2, Calls.Step>}
  -after = {Laws.moved(storage, who, limit, logs, world, Nat.add(Laws.shares(storage, who), amount), Nat.add(Laws.total(storage), amount)) : Evm.State}
  -rhs = {Bool.pick(Evm.Outcome<Unit>, Evm.same.call(q, Evm.Call{Laws.token(storage), "transferFrom", [who, Evm.self.of(world), amount]}),
      Evm.Ok{Unit{}, Calls.after(Unit, after, Calls.drive(Calls.Model{}, Cert.entry.table(), cbs, Unit, True{}, Evm.Ok{Unit{}, after}))},
      Evm.Revert{}) : Evm.Outcome<Unit>}
  %e1 : {Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, False{}, Bool.pick(Evm.Outcome<Unit>, _,
    Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.total(storage), amount), limit), taking(storage, who, limit, logs, world, amount), Evm.Revert{}),
    Evm.Revert{})) == rhs : Evm.Outcome<Unit>}
  %e2 : {Calls.drive(Calls.Model{}, Cert.entry.table(), steps, Unit, False{},
    Bool.pick(Evm.Outcome<Unit>, _, taking(storage, who, limit, logs, world, amount), Evm.Revert{})) == rhs : Evm.Outcome<Unit>}
  {==}

def Laws.touch(storage, who, limit, logs, world, q, other, x, y):
  {==}
