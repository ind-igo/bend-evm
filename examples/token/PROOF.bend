import Base
import ../../src/Evm.bend as Evm
import ./program.bend as Token
import ./LAWS.bend as Laws

# Each checked step stops at a Bool that a hypothesis fixes. A rewrite names
# the rest of the program with one of these defs, then the program computes.

def transfer.finish(+amount: Nat) -> Nat -> Evm.Contract(Nat):
  sum => do Evm.Contract<Nat>:
    Evm.store(1n, 9n, sum)
    Evm.log(Token.transfer_event(), [8n, 9n], amount)
    Evm.Contract.pure(Nat, 1n)

def transfer.credit(+amount: Nat) -> Nat -> Evm.Contract(Nat):
  rest => do Evm.Contract<Nat>:
    Evm.store(1n, 8n, rest)
    b : Nat <- Evm.load(1n, 9n)
    sum : Nat <- Evm.add(b, amount)
    transfer.finish(amount, sum)

def mint.finish(+amount: Nat) -> Nat -> Evm.Contract(Unit):
  sum => do Evm.Contract<Unit>:
    Evm.store(1n, 9n, sum)
    Evm.log(Token.transfer_event(), [0n, 9n], amount)

def mint.credit(+amount: Nat) -> Nat -> Evm.Contract(Unit):
  total => do Evm.Contract<Unit>:
    Evm.sstore(0n, total)
    b : Nat <- Evm.load(1n, 9n)
    sum : Nat <- Evm.add(b, amount)
    mint.finish(amount, sum)

def Laws.transfer_moves(storage, limit, logs, a, b, amount, enough, fits):
  +start = {Evm.Slot{Evm.Mapped{1n, 8n}, a} <> Evm.Slot{Evm.Mapped{1n, 9n}, b} <> storage : List<&2, Evm.Slot>}
  +debited = {Evm.Slot{Evm.Mapped{1n, 8n}, Nat.sub(a, amount)} <> start : List<&2, Evm.Slot>}
  +after = {Evm.Ok{1n, Evm.State{Evm.Slot{Evm.Mapped{1n, 9n}, Nat.add(b, amount)} <> debited, 8n, limit,
    Evm.Log{"Transfer(address,address,uint256)", [8n, 9n], amount} <> logs}} : Evm.Outcome<Nat>}
  %enough : {Evm.Contract.next(Nat, Nat, Evm.checked(Nat.sub(a, amount), Bool.not(_), Evm.State{start, 8n, limit, logs}),
    transfer.credit(amount)) == after : Evm.Outcome<Nat>}
  %fits : {Evm.Contract.next(Nat, Nat, Evm.checked(Nat.add(b, amount), _, Evm.State{debited, 8n, limit, logs}),
    transfer.finish(amount)) == after : Evm.Outcome<Nat>}
  {==}

def Laws.transfer_short(storage, limit, logs, a, b, amount, short):
  +start = {Evm.Slot{Evm.Mapped{1n, 8n}, a} <> Evm.Slot{Evm.Mapped{1n, 9n}, b} <> storage : List<&2, Evm.Slot>}
  %short : {Evm.Contract.next(Nat, Nat, Evm.checked(Nat.sub(a, amount), Bool.not(_), Evm.State{start, 8n, limit, logs}),
    transfer.credit(amount)) == Evm.Revert{} : Evm.Outcome<Nat>}
  {==}

def Laws.mint_by_owner(storage, limit, logs, supply, b, amount, room, fits):
  +start = {Evm.Slot{Evm.Plain{0n}, supply} <> Evm.Slot{Evm.Mapped{1n, 9n}, b} <> storage : List<&2, Evm.Slot>}
  +raised = {Evm.Slot{Evm.Plain{0n}, Nat.add(supply, amount)} <> start : List<&2, Evm.Slot>}
  +after = {Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Mapped{1n, 9n}, Nat.add(b, amount)} <> raised, 7n, limit,
    Evm.Log{"Transfer(address,address,uint256)", [0n, 9n], amount} <> logs}} : Evm.Outcome<Unit>}
  %room : {Evm.Contract.next(Nat, Unit, Evm.checked(Nat.add(supply, amount), _, Evm.State{start, 7n, limit, logs}),
    mint.credit(amount)) == after : Evm.Outcome<Unit>}
  %fits : {Evm.Contract.next(Nat, Unit, Evm.checked(Nat.add(b, amount), _, Evm.State{raised, 7n, limit, logs}),
    mint.finish(amount)) == after : Evm.Outcome<Unit>}
  {==}

def Laws.mint_by_other(storage, limit, logs, to, amount):
  {==}
