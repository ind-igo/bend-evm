import Base
import ./ir.bend as IR
import ./read.bend as Read
import ./tool.bend as Tool

# Prints the ABI JSON of the named contract functions, for wallets, explorers
# and tools such as cast. An entry named init is the constructor. The events
# are the ones the functions log. Like the dispatcher, this is tested, not
# proved. Usage: abi.bend <contract.bend> <function>...

def quote(s: String) -> String:
  "\"" ++ s ++ "\""

def field(+key: String, +value: String) -> String:
  quote(key) ++ ":" ++ value

def join(items: List<&2, String>) -> String:
  String.join(items, ",")

def param(+name: String, +typ: String) -> String:
  "{" ++ field("name", quote(name)) ++ "," ++ field("type", quote(typ)) ++ "}"

def params(inputs: List<&2, Read.Input>) -> List<&2, String>:
  match inputs:
    case Nil{}:
      Nil{}
    case Read.Input{+n, +t} <> rest:
      param(n, t) <> params(rest)

# A result's outputs: none for Unit, whose ABI type is "".
def outputs(+typ: String) -> String:
  Bool.pick(String, String.is_empty(typ), "[]", "[" ++ param("", typ) ++ "]")

def writes.effect(e: IR.Effect) -> Bool:
  match e:
    case IR.Require{_}:
      False{}
    case _:
      True{}

# A function that stores or logs is nonpayable; one that only reads is view.
def writes(cmd: IR.Cmd) -> Bool:
  match cmd:
    case IR.Bind{_, _, body}:
      writes(body)
    case IR.Then{e, body}:
      Bool.or(writes.effect(e), writes(body))
    case IR.Finish{e}:
      writes.effect(e)
    case IR.If{_, yes, no}:
      Bool.or(writes(yes), writes(no))
    case _:
      False{}

def mutability(+w: Bool) -> String:
  Bool.pick(String, w, "nonpayable", "view")

def function.text(+name: String, +inputs: List<&2, String>, +output: String, +state: String) -> String:
  "{" ++ join([field("type", quote("function")), field("name", quote(name)), field("inputs", "[" ++ join(inputs) ++ "]"),
    field("outputs", outputs(output)), field("stateMutability", quote(state))]) ++ "}"

def constructor.text(+inputs: List<&2, String>) -> String:
  "{" ++ join([field("type", quote("constructor")), field("inputs", "[" ++ join(inputs) ++ "]"),
    field("stateMutability", quote("nonpayable"))]) ++ "}"

# An event that a function logs: its signature and the number of indexed words.
# A log does not say which parameters its topics are, so the first ones are
# indexed; the README asks for indexed parameters first.
type Emitted is Data:
  Emitted{signature: String, indexed: Nat}

def events(cmd: IR.Cmd) -> List<&2, Emitted>:
  match cmd:
    case IR.Bind{_, _, body}:
      events(body)
    case IR.Then{IR.Log{event, topics, _}, body}:
      Emitted{event, List.length(&2, IR.Expr, topics)} <> events(body)
    case IR.Then{_, body}:
      events(body)
    case IR.Finish{IR.Log{event, topics, _}}:
      [Emitted{event, List.length(&2, IR.Expr, topics)}]
    case IR.If{_, yes, no}:
      List.append(&2, Emitted, events(yes), events(no))
    case _:
      Nil{}

def known(+signature: String, seen: List<&2, Emitted>) -> Bool:
  match seen:
    case Nil{}:
      False{}
    case Emitted{s, _} <> rest:
      Bool.or(String.eq(s, signature), known(signature, rest))

# Whether seen has the signature with another number of indexed words.
def clash(+signature: String, +indexed: Nat, seen: List<&2, Emitted>) -> Bool:
  match seen:
    case Nil{}:
      False{}
    case Emitted{s, +n} <> rest:
      Bool.or(Bool.and(String.eq(s, signature), Bool.not(Nat.is_eq(n, indexed))), clash(signature, indexed, rest))

def unique.cons(+e: Emitted, r: Result<&2, &2, String, List<&2, Emitted>>) -> Result<&2, &2, String, List<&2, Emitted>>:
  do Result<&2, &2, String, List<&2, Emitted>>:
    rest : List<&2, Emitted> <- r
    return e <> rest

# Each signature once. Two events with one signature have one topic 0, so
# they must agree on their indexed parameters, as Solidity requires.
def unique(found: List<&2, Emitted>, +seen: List<&2, Emitted>) -> Result<&2, &2, String, List<&2, Emitted>>:
  match found:
    case Nil{}:
      Done{Nil{}}
    case Emitted{+s, +n} <> rest:
      +old = known(s, seen)
      +r = unique(rest, Bool.pick(List<&2, Emitted>, old, seen, Emitted{s, n} <> seen))
      Bool.pick(Result<&2, &2, String, List<&2, Emitted>>, clash(s, n, seen),
        Fail{"Two events have the signature " ++ s ++ " but different indexed parameters"},
        Bool.pick(Result<&2, &2, String, List<&2, Emitted>>, old, r, unique.cons(Emitted{s, n}, r)))

def upto(s: String, +stop: Char) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, rest}:
      Bool.pick(String, Char.is_eq(c, stop), "", SCon{c, upto(rest, stop)})

def from(s: String, +start: Char) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{c, +rest}:
      Bool.pick(String, Char.is_eq(c, start), rest, from(rest, start))

def event.inputs(types: List<&2, String>, +indexed: Nat) -> List<&2, String>:
  match types:
    case Nil{}:
      Nil{}
    case +t <> rest:
      +flag = Bool.pick(String, Nat.is_eq(indexed, 0n), "false", "true")
      ("{" ++ join([field("name", quote("")), field("type", quote(t)), field("indexed", flag)]) ++ "}")
        <> event.inputs(rest, Nat.sub(indexed, 1n))

def event.text(e: Emitted) -> String:
  match e:
    case Emitted{+signature, indexed}:
      +inner = upto(from(signature, '('), ')')
      +types = Bool.pick(List<&2, String>, String.is_empty(inner), Nil{}, String.split(inner, ','))
      "{" ++ join([field("type", quote("event")), field("name", quote(upto(signature, '('))),
        field("inputs", "[" ++ join(event.inputs(types, indexed)) ++ "]"), field("anonymous", "false")]) ++ "}"

def event.texts(es: List<&2, Emitted>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      event.text(e) <> event.texts(rest)

# One entry's ABI item, and the events it logs.
type Item is Data:
  Item{text: String, events: List<&2, Emitted>}

def item.contract(+name: String, inputs: List<&2, Read.Input>, +output: String, +body: IR.Cmd) -> Item:
  +ins = params(inputs)
  Item{Bool.pick(String, String.eq(name, "init"), constructor.text(ins),
    function.text(name, ins, output, mutability(writes(body)))), events(body)}

def item(f: Read.Function) -> Item:
  match f:
    case Read.Constant{+name, _}:
      Item{function.text(name, Nil{}, "string", "pure"), Nil{}}
    case Read.Contract{+name, inputs, +output, Read.Entry{_, +body}}:
      item.contract(name, inputs, output, body)

type Items is Data:
  Items{texts: List<&2, String>, events: List<&2, Emitted>}

def items.add(i: Item, rest: Items) -> Items:
  match i rest:
    case Item{t, es} Items{ts, found}:
      Items{t <> ts, List.append(&2, Emitted, es, found)}

def items(fs: List<&2, Read.Function>) -> Items:
  match fs:
    case Nil{}:
      Items{Nil{}, Nil{}}
    case f <> rest:
      items.add(item(f), items(rest))

def document(all: Items) -> Result<&2, &2, String, String>:
  match all:
    case Items{texts, found}:
      do Result<&2, &2, String, String>:
        es : List<&2, Emitted> <- unique(found, Nil{})
        return "[" ++ join(List.append(&2, String, texts, event.texts(es))) ++ "]\n"

def abi(file: String, s: Tool.Setup) -> Result<&2, &2, String, String>:
  match s:
    case Tool.Setup{_, fs}:
      document(items(fs))

def main() -> IO(Unit):
  Tool.main(~abi, "Usage: abi.bend <contract.bend> <function>...")
