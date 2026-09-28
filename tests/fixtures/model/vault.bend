import Base
import ../../../src/Evm.bend as Evm
import ../../../src/calls.bend as Calls
import ../vault/CERT.bend as Cert

# Runs the vault's certified entries with Calls.drive, for the differential
# test against anvil. Each transaction is a callback from outside, with the
# answers and callbacks that anvil's call trace gives. The first argument is
# the limit; the rest are tokens in postfix order, read with a stack:
#
#   a number        a word
#   [               the start of a list
#   ]w  ]s          the end of a list of words, or of steps
#   E               sender entry [args]w [answers]s -> Enter
#   A               target name [args]w [callbacks]s value -> Answer
#   T               runs the Enter on top as a transaction
#   any other text  a function name
#
# For each transaction it prints "ok" or "revert", then the shares of the
# accounts 1 to 4, the total and slot 3. Account 2 is the token, and 3 is
# the vault.

type Item is Data:
  Word{n: Nat}
  Name{s: String}
  Mark{}
  Words{ws: List<&2, Nat>}
  Steps{ss: List<&2, Calls.Step>}
  One{step: Calls.Step}

type Run is Data:
  Run{text: String, stack: List<&2, Item>, state: Evm.State}

def words(stack: List<&2, Item>, acc: List<&2, Nat>) -> List<&2, Item>:
  match stack:
    case Nil{}:
      [Words{acc}]
    case Word{n} <> rest:
      words(rest, n <> acc)
    case Mark{} <> rest:
      Words{acc} <> rest
    case _ <> rest:
      words(rest, acc)

def steps(stack: List<&2, Item>, acc: List<&2, Calls.Step>) -> List<&2, Item>:
  match stack:
    case Nil{}:
      [Steps{acc}]
    case One{s} <> rest:
      steps(rest, s <> acc)
    case Mark{} <> rest:
      Steps{acc} <> rest
    case _ <> rest:
      steps(rest, acc)

def enter(stack: List<&2, Item>) -> List<&2, Item>:
  match stack:
    case Steps{answers} <> Words{args} <> Word{entry} <> Word{sender} <> rest:
      One{Calls.Enter{sender, entry, args, answers}} <> rest
    case _:
      []

def answer(stack: List<&2, Item>) -> List<&2, Item>:
  match stack:
    case Word{value} <> Steps{callbacks} <> Words{args} <> Name{name} <> Word{target} <> rest:
      One{Calls.Answer{Evm.Call{target, name, args}, callbacks, value}} <> rest
    case _:
      []

def ok(o: Evm.Outcome<Unit>) -> String:
  match o:
    case Evm.Ok{_, _}:
      "ok"
    case _:
      "revert"

def show(+storage: List<&2, Evm.Slot>) -> String:
  " " ++ Nat.show(Evm.lookup(storage, Evm.Mapped{Evm.Plain{0n}, 1n}))
    ++ " " ++ Nat.show(Evm.lookup(storage, Evm.Mapped{Evm.Plain{0n}, 2n}))
    ++ " " ++ Nat.show(Evm.lookup(storage, Evm.Mapped{Evm.Plain{0n}, 3n}))
    ++ " " ++ Nat.show(Evm.lookup(storage, Evm.Mapped{Evm.Plain{0n}, 4n}))
    ++ " " ++ Nat.show(Evm.lookup(storage, Evm.Plain{1n}))
    ++ " " ++ Nat.show(Evm.lookup(storage, Evm.Plain{3n})) ++ "\n"

# One transaction: the text, and the state after it.
def done(o: Evm.Outcome<Unit>, s: Evm.State) -> Run:
  match o:
    case Evm.Ok{_, Evm.State{+storage, caller, limit, logs, world}}:
      Run{"ok" ++ show(storage), [], Evm.State{storage, caller, limit, logs, world}}
    case _:
      match s:
        case Evm.State{+storage, caller, limit, logs, world}:
          Run{"revert" ++ show(storage), [], Evm.State{storage, caller, limit, logs, world}}

def transact(stack: List<&2, Item>, +s: Evm.State) -> Run:
  match stack:
    case One{Calls.Enter{sender, i, args, answers}} <> _:
      done(Calls.drive(Calls.Model{}, Cert.entry.table(), answers, Unit, False{},
        Calls.callback(Calls.Model{}, Cert.entry.table(), i, args, Unit, u => w => Evm.Ok{u, w}, Calls.with.caller(sender, s))), s)
    case _:
      Run{"bad transaction\n", [], s}

def symbol(+t: String, +stack: List<&2, Item>) -> List<&2, Item>:
  Bool.pick(List<&2, Item>, String.eq(t, "["), Mark{} <> stack,
    Bool.pick(List<&2, Item>, String.eq(t, "]w"), words(stack, []),
      Bool.pick(List<&2, Item>, String.eq(t, "]s"), steps(stack, []),
        Bool.pick(List<&2, Item>, String.eq(t, "E"), enter(stack),
          Bool.pick(List<&2, Item>, String.eq(t, "A"), answer(stack), Name{t} <> stack)))))

def read(n: Maybe<&2, Nat>, +t: String, +stack: List<&2, Item>) -> List<&2, Item>:
  match n:
    case Some{x}:
      Word{x} <> stack
    case None{}:
      symbol(t, stack)

def token(+t: String, stack: List<&2, Item>) -> List<&2, Item>:
  read(Nat.read(t), t, stack)

def prepend(before: String, r: Run) -> Run:
  match r:
    case Run{text, stack, s}:
      Run{before ++ text, stack, s}

def next(+t: String, r: Run) -> Run:
  match r:
    case Run{+text, +stack, +s}:
      Bool.pick(Run, String.eq(t, "T"), prepend(text, transact(stack, s)), Run{text, token(t, stack), s})

def go(tokens: List<String>, r: Run) -> String:
  match tokens r:
    case t <> rest _:
      go(rest, next(t, r))
    case Nil{} Run{text, _, _}:
      text

def start(args: List<String>) -> String:
  match args:
    case limit <> tokens:
      go(tokens, Run{"", [], Evm.State{[Evm.Slot{Evm.Plain{2n}, 2n}], 0n, Maybe.default(&2, Nat, Nat.read(limit), 0n), [],
        Evm.World{0n, 0n, 3n, [], [], []}}})
    case Nil{}:
      ""

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.write(start(List.tail(&1, String, args))) # the first is the program
