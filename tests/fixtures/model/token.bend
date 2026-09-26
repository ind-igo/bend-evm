import Base
import ../../../src/Evm.bend as Evm
import ../../../examples/token/program.bend as Token

# Runs the token's Bend source on a sequence of calls, for the differential
# test against anvil. The arguments are groups of five: the caller, the
# function, and three words (unused words are 0). The first argument is the
# limit, below 2^48 as the runtime needs. For each call it prints "ok",
# "ok <word>", "revert" or "revert <error> <words>", then each new log,
# oldest first, as "log <event> <topics> | <data>".

type Step is Data:
  Step{text: String, state: Evm.State}

def num(text: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(text), 0n)

def words(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case +x <> rest:
      " " ++ Nat.show(x) ++ words(rest)

def show.logs(logs: List<&2, Evm.Log>) -> String:
  match logs:
    case Nil{}:
      ""
    case Evm.Log{event, topics, data} <> rest:
      show.logs(rest) ++ "log " ++ event ++ words(topics) ++ " |" ++ words(data) ++ "\n"

def show.word(n: Nat) -> String:
  " " ++ Nat.show(n)

def show.unit(u: Unit) -> String:
  ""

# A revert keeps the state from before the call.
def after(-A: Data, show: A -> String, o: Evm.Outcome<A>, +before: Evm.State) -> Step:
  match o:
    case Evm.Ok{value, Evm.State{storage, caller, limit, logs, world}}:
      Step{"ok" ++ show(value) ++ "\n" ++ show.logs(logs), Evm.State{storage, caller, limit, [], world}}
    case Evm.Revert{}:
      Step{"revert\n", before}
    case Evm.Raise{Evm.Error{error, args}}:
      Step{"revert " ++ error ++ words(args) ++ "\n", before}

def call(-A: Data, show: A -> String, m: Evm.Contract(A), +who: Nat, s: Evm.State) -> Step:
  match s:
    case Evm.State{+storage, _, +limit, _, +world}:
      after(A, show, Evm.run(A, m, Evm.State{storage, who, limit, [], world}), Evm.State{storage, who, limit, [], world})

def one(name: String, +who: Nat, +a: Nat, +b: Nat, +c: Nat, s: Evm.State) -> Step:
  match name:
    case "init":
      call(Unit, show.unit, Token.init(a), who, s)
    case "owner":
      call(Nat, show.word, Token.owner(), who, s)
    case "transferOwnership":
      call(Unit, show.unit, Token.transferOwnership(a), who, s)
    case "totalSupply":
      call(Nat, show.word, Token.totalSupply(), who, s)
    case "balanceOf":
      call(Nat, show.word, Token.balanceOf(a), who, s)
    case "transfer":
      call(Nat, show.word, Token.transfer(a, b), who, s)
    case "mint":
      call(Unit, show.unit, Token.mint(a, b), who, s)
    case "allowance":
      call(Nat, show.word, Token.allowance(a, b), who, s)
    case "approve":
      call(Nat, show.word, Token.approve(a, b), who, s)
    case "transferFrom":
      call(Nat, show.word, Token.transferFrom(a, b, c), who, s)
    case "burn":
      call(Unit, show.unit, Token.burn(a), who, s)
    case _:
      Step{"unknown\n", s}

def steps(calls: List<String>, step: Step) -> String:
  match calls step:
    case who <> name <> a <> b <> c <> rest Step{text, state}:
      text ++ steps(rest, one(name, num(who), num(a), num(b), num(c), state))
    case _ Step{text, _}:
      text

def start(args: List<String>) -> String:
  match args:
    case limit <> calls:
      steps(calls, Step{"", Evm.State{[], 0n, num(limit), [], Evm.World{0n, 0n, 0n, [], []}}})
    case Nil{}:
      ""

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.write(start(args))
