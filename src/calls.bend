import Base
import ./Evm.bend as Evm
import ./ir.bend as IR
import ./yul.bend as Yul

# Runs a contract that makes calls that may write (Evm.call). Such a call
# stops the contract as Evm.Calling. The run then takes the next answer:
# the callbacks that the called contract makes into this one while the call
# runs, then the word it returns. Each callback runs one of this contract's
# entries, from any sender, with its own answers for the calls that it
# makes. A callback that reverts changes nothing, as the caller may catch
# that. The answers are a tree, so every run ends.
#
# A law holds for every list of answers, so it holds for every called
# contract and every callback that it makes. A real run gives one list: a
# callback that the EVM rejects before the entry runs, such as one with a
# bad selector or a bad argument, changes nothing and is not in the list.
# A callback's args are the ABI encoding of its arguments.
type Step is Data:
  Answer{call: Evm.Call, callbacks: List<&2, Step>, value: Nat}
  Enter{sender: Nat, entry: Nat, args: List<&2, Nat>, answers: List<&2, Step>}

# The kind of a parameter: a word, or bytes, which the ABI encodes after the
# words.
type Param is Data:
  Word{}
  Dynamic{}

# An entry that a callback can run: its IR, its output, and the kinds of its
# parameters, which have the levels 0, 1, ... in order. The certificate's
# entry.table lists the contract's entries, and a callback names one by its
# index in that list.
type Entry is Data:
  Entry{cmd: IR.Cmd, out: IR.Output, params: List<&2, Param>}

# The code that a callback runs: the IR, or its Yul lowering.
type Code is Data:
  Model{}
  Lowered{}

def entry(entries: List<&2, Entry>, +i: Nat) -> Maybe<&2, Entry>:
  match entries i:
    case Nil{} _:
      None{}
    case e <> _ 0n:
      Some{e}
    case _ <> rest 1n+j:
      entry(rest, j)

def bind.cons(+b: IR.Binding, env: Maybe<&2, List<&2, IR.Binding>>) -> Maybe<&2, List<&2, IR.Binding>>:
  match env:
    case Some{bs}:
      Some{b <> bs}
    case None{}:
      None{}

def bind.blob(+level: Nat, b: Maybe<&2, Evm.Bytes>, env: Maybe<&2, List<&2, IR.Binding>>) -> Maybe<&2, List<&2, IR.Binding>>:
  match b:
    case Some{v}:
      bind.cons(IR.Blob{level, v}, env)
    case None{}:
      None{}

def taken.cons(+w: Nat, ws: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match ws:
    case Some{xs}:
      Some{w <> xs}
    case None{}:
      None{}

# The first n words, if there are n.
def take(n: Nat, ws: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match n ws:
    case 0n _:
      Some{Nil{}}
    case 1n+_ Nil{}:
      None{}
    case 1n+m w <> rest:
      taken.cons(w, take(m, rest))

def made(+length: Nat, ws: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, Evm.Bytes>:
  match ws:
    case Some{xs}:
      Some{Evm.Bytes{length, xs}}
    case None{}:
      None{}

def decode.at(ws: List<&2, Nat>) -> Maybe<&2, Evm.Bytes>:
  match ws:
    case Nil{}:
      None{}
    case +n <> rest:
      made(n, take(Nat.div(Nat.add(n, 31n), 32n), rest))

# The bytes at offset in an ABI encoding: the length, then its words. The
# dispatcher rejects an offset that is not a multiple of 32, and bytes
# past the end.
def decode(+offset: Nat, all: List<&2, Nat>) -> Maybe<&2, Evm.Bytes>:
  Bool.pick(Maybe<&2, Evm.Bytes>, Nat.is_eq(Nat.mod(offset, 32n), 0n),
    decode.at(List.drop(&2, Nat, all, Nat.div(offset, 32n))), None{})

# The parameters from level on, bound to the arguments: a word parameter to
# its word, and a bytes parameter to the bytes at the offset that its word
# gives in all, the whole encoding. Too few words is a bad call; words after
# the last parameter are ignored, as the ABI decoder ignores them.
def bind(params: List<&2, Param>, +level: Nat, heads: List<&2, Nat>, +all: List<&2, Nat>) -> Maybe<&2, List<&2, IR.Binding>>:
  match params heads:
    case Nil{} _:
      Some{Nil{}}
    case _ <> _ Nil{}:
      None{}
    case Word{} <> ps a <> rest:
      bind.cons(IR.Binding{level, a}, bind(ps, 1n+level, rest, all))
    case Dynamic{} <> ps a <> rest:
      bind.blob(level, decode(a, all), bind(ps, 1n+level, rest, all))

def start(code: Code, +cmd: IR.Cmd, +out: IR.Output, +env: List<&2, IR.Binding>) -> Evm.Contract(IR.value(out)):
  match code:
    case Model{}:
      IR.call(cmd, out, env)
    case Lowered{}:
      Bool.pick(Evm.Contract(IR.value(out)), IR.closed(cmd, IR.levels(env)), Yul.exec(Yul.lower(cmd, out), out, env),
        IR.abort(IR.value(out)))

def started(+code: Code, +cmd: IR.Cmd, +out: IR.Output, env: Maybe<&2, List<&2, IR.Binding>>) -> Evm.Contract(Unit):
  match env:
    case Some{+bs}:
      Evm.Contract.bind(IR.value(out), Unit, start(code, cmd, out, bs), _ => Evm.Contract.pure(Unit, Unit{}))
    case None{}:
      IR.abort(Unit)

def found(+code: Code, e: Maybe<&2, Entry>, +args: List<&2, Nat>) -> Evm.Contract(Unit):
  match e:
    case Some{Entry{+cmd, +out, params}}:
      started(code, cmd, out, bind(params, 0n, args, args))
    case None{}:
      IR.abort(Unit)

# The entry that a callback runs, with its result dropped.
def callback(+code: Code, +entries: List<&2, Entry>, +i: Nat, args: List<&2, Nat>) -> Evm.Contract(Unit):
  found(code, entry(entries, i), args)

def with.caller(+who: Nat, s: Evm.State) -> Evm.State:
  match s:
    case Evm.State{storage, _, limit, logs, world}:
      Evm.State{storage, who, limit, logs, world}

# The state after the callbacks of an answer.
def after(-A: Data, s: Evm.State, o: Evm.Outcome<A>) -> Evm.State:
  match o:
    case Evm.Ok{_, t}:
      t
    case Evm.Revert{}:
      s
    case Evm.Raise{_}:
      s
    case Evm.Calling{_, _, _}:
      s

# The state after one callback: its state with this call's caller back, or
# the state before it if it reverted.
def back(-A: Data, +s: Evm.State, o: Evm.Outcome<A>) -> Evm.State:
  match o:
    case Evm.Ok{_, t}:
      with.caller(Evm.caller.of(s), t)
    case Evm.Revert{}:
      s
    case Evm.Raise{_}:
      s
    case Evm.Calling{_, _, _}:
      s

# The end of a run: a call with no answer reverts.
def stop(-A: Data, o: Evm.Outcome<A>) -> Evm.Outcome<A>:
  match o:
    case Evm.Ok{v, s}:
      Evm.Ok{v, s}
    case Evm.Revert{}:
      Evm.Revert{}
    case Evm.Raise{e}:
      Evm.Raise{e}
    case Evm.Calling{_, _, _}:
      Evm.Revert{}

# Runs o with the steps. When open, the steps are callbacks that run after
# o succeeds; otherwise they answer o's calls, and an answer whose call
# differs reverts, so a law checks each call.
def drive(+code: Code, +entries: List<&2, Entry>, steps: List<&2, Step>, -A: Data, open: Bool, o: Evm.Outcome<A>) -> Evm.Outcome<A>:
  match steps:
    case Nil{}:
      stop(A, o)
    case step <> rest:
      match step:
        case Enter{+sender, +i, +args, inner}:
          match open:
            case True{}:
              match o:
                case Evm.Ok{v, +s}:
                  +t = back(Unit, s, drive(code, entries, inner, Unit, False{},
                    callback(code, entries, i, args, Unit, u => w => Evm.Ok{u, w}, with.caller(sender, s))))
                  drive(code, entries, rest, A, True{}, Evm.Ok{v, t})
                case Evm.Revert{}:
                  Evm.Revert{}
                case Evm.Raise{e}:
                  Evm.Raise{e}
                case Evm.Calling{_, _, _}:
                  Evm.Revert{}
            case False{}:
              stop(A, o)
        case Answer{q, cbs, x}:
          match open:
            case True{}:
              stop(A, o)
            case False{}:
              match o:
                case Evm.Ok{v, s}:
                  Evm.Ok{v, s}
                case Evm.Revert{}:
                  Evm.Revert{}
                case Evm.Raise{e}:
                  Evm.Raise{e}
                case Evm.Calling{c, +s, r}:
                  Bool.pick(Evm.Outcome<A>, Evm.same.call(q, c),
                    drive(code, entries, rest, A, False{}, r(x, after(Unit, s, drive(code, entries, cbs, Unit, True{}, Evm.Ok{Unit{}, s})))),
                    Evm.Revert{})

# Runs a contract from a state with the entries and the answers, as Evm.run
# does for a contract with no calls that may write.
def run(+entries: List<&2, Entry>, -A: Data, m: Evm.Contract(A), steps: List<&2, Step>, s: Evm.State) -> Evm.Outcome<A>:
  drive(Model{}, entries, steps, A, False{}, m(A, x => t => Evm.Ok{x, t}, s))
