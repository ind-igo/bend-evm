import Base
import ../../../src/Evm.bend as Evm

# Runs the model's word operations (Evm.op), for the test against the
# reference in tests/evm.js. The first argument is the limit. Then each
# case is its words and then the operation's Yul name, such as "3 5 add";
# it prints the result of each case on its own line.

def yul(i: Evm.Info) -> String:
  match i:
    case Evm.Info{_, y, _, _}:
      y

def find(ops: List<&2, Evm.Op>, +name: String) -> Maybe<&2, Evm.Op>:
  match ops:
    case Nil{}:
      None{}
    case +o <> rest:
      Bool.pick(Maybe<&2, Evm.Op>, String.eq(yul(Evm.info(o)), name), Some{o}, find(rest, name))

def result(found: Maybe<&2, Evm.Op>, words: List<&2, Nat>, +limit: Nat) -> String:
  match found:
    case Some{o}:
      Nat.show(Evm.op(o, List.reverse(&2, Nat, words), limit)) ++ "\n"
    case None{}:
      "unknown\n"

type Run is Data:
  Run{stack: List<&2, Nat>, out: String}

def word(n: Maybe<&2, Nat>, +t: String, +stack: List<&2, Nat>, out: String, +limit: Nat) -> Run:
  match n:
    case Some{x}:
      Run{x <> stack, out}
    case None{}:
      Run{[], out ++ result(find(Evm.ops(), t), stack, limit)}

def next(+t: String, r: Run, +limit: Nat) -> Run:
  match r:
    case Run{stack, out}:
      word(Nat.read(t), t, stack, out, limit)

def go(tokens: List<String>, r: Run, +limit: Nat) -> String:
  match tokens r:
    case +t <> rest _:
      go(rest, next(t, r, limit), limit)
    case Nil{} Run{_, out}:
      out

def start(args: List<String>) -> String:
  match args:
    case limit <> tokens:
      go(tokens, Run{[], ""}, Maybe.default(&2, Nat, Nat.read(limit), 0n))
    case Nil{}:
      ""

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.write(start(List.tail(&1, String, args)))
