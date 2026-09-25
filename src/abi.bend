import Base
import ../vendor/bend-frontend/src/core.bend as Core
import ../vendor/bend-frontend/src/frontend.bend as Frontend
import ./ir.bend as IR
import ./read.bend as Read
import ./certify.bend as Certify

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

def params(names: List<&2, String>, types: List<&2, String>) -> List<&2, String>:
  match names types:
    case +n <> ns +t <> ts:
      param(n, t) <> params(ns, ts)
    case _ _:
      Nil{}

# The parameter names, from the binders of the declared type.
def names(arity: Nat, typ: Core.Term) -> List<&2, String>:
  match arity typ:
    case n Core.TAnn{value, _}:
      names(n, value)
    case 1n+p Core.TAll{_, name, _, _, body}:
      name <> names(p, body)
    case _ _:
      Nil{}

def names.found(found: Maybe<&2, Core.Declaration>) -> List<&2, String>:
  match found:
    case Some{Core.Definition{Core.Header{_, _, arity, typ}, _, _, _, _, _}}:
      names(U32.to_nat(arity), typ)
    case _:
      Nil{}

# The ABI type of a result: "" for Unit.
def result.name(+name: String) -> Result<&2, &2, String, String>:
  match name:
    case "Unit":
      Done{""}
    case other:
      Read.abi(other)

def result.term(+evm: String, typ: Core.Term) -> Result<&2, &2, String, String>:
  match typ:
    case Core.TAnn{value, _}:
      result.term(evm, value)
    case Core.TRef{+name, _}:
      result.name(Read.canonical(Read.after(evm, name), name))
    case _:
      Fail{"Unsupported result type"}

def result.call(+evm: String, c: Read.Call) -> Result<&2, &2, String, String>:
  match c:
    case Read.Call{_, arg <> Nil{}}:
      result.term(evm, arg)
    case _:
      Fail{"Expected an Evm.Contract result"}

def result(+evm: String, arity: Nat, typ: Core.Term) -> Result<&2, &2, String, String>:
  match arity typ:
    case n Core.TAnn{value, _}:
      result(evm, n, value)
    case 0n body:
      result.call(evm, Read.call(Core.bare(body), Nil{}))
    case 1n+p Core.TAll{_, _, _, _, body}:
      result(evm, p, body)
    case _ _:
      Fail{"Expected an Evm.Contract result"}

def result.found(found: Maybe<&2, Core.Declaration>, +evm: String) -> Result<&2, &2, String, String>:
  match found:
    case Some{Core.Definition{Core.Header{_, _, arity, typ}, _, _, _, _, _}}:
      result(evm, U32.to_nat(arity), typ)
    case _:
      Fail{"Unknown contract function"}

def outputs(typ: String) -> String:
  match typ:
    case "":
      "[]"
    case +t:
      "[" ++ param("", t) ++ "]"

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
    case _:
      Nil{}

def known(+signature: String, seen: List<&2, Emitted>) -> Bool:
  match seen:
    case Nil{}:
      False{}
    case Emitted{s, _} <> rest:
      Bool.or(String.eq(s, signature), known(signature, rest))

def unique(found: List<&2, Emitted>, +seen: List<&2, Emitted>) -> List<&2, Emitted>:
  match found:
    case Nil{}:
      Nil{}
    case Emitted{+s, +n} <> +rest:
      Bool.pick(List<&2, Emitted>, known(s, seen), unique(rest, seen), Emitted{s, n} <> unique(rest, Emitted{s, n} <> seen))

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

def item.text(+name: String, entry: Read.Entry, +inputs: List<&2, String>, +output: String) -> Item:
  match entry:
    case Read.Entry{_, +body}:
      Item{Bool.pick(String, String.eq(name, "init"), constructor.text(inputs),
        function.text(name, inputs, output, mutability(writes(body)))), events(body)}

def item.contract(+name: String, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, Item>:
  do Result<&2, &2, String, Item>:
    entry : Read.Entry <- Read.entry(evm, decls, name)
    types : List<&2, String> <- Read.types(evm, decls, name)
    output : String <- result.found(Core.find(decls, name), evm)
    return item.text(name, entry, params(names.found(Core.find(decls, name)), types), output)

def item(+name: String, found: Maybe<&2, String>, +evm: String, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, Item>:
  match found:
    case Some{_}:
      Done{Item{function.text(name, Nil{}, "string", "pure"), Nil{}}}
    case None{}:
      item.contract(name, evm, decls)

type Items is Data:
  Items{texts: List<&2, String>, events: List<&2, Emitted>}

def items.add(i: Item, rest: Items) -> Items:
  match i rest:
    case Item{t, es} Items{ts, found}:
      Items{t <> ts, List.append(&2, Emitted, es, found)}

def items(names: List<&2, String>, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, Items>:
  match names:
    case Nil{}:
      Done{Items{Nil{}, Nil{}}}
    case +name <> rest:
      do Result<&2, &2, String, Items>:
        head : Item <- item(name, Read.string_entry(decls, name), evm, decls)
        tail : Items <- items(rest, evm, decls)
        return items.add(head, tail)

def document(all: Items) -> String:
  match all:
    case Items{texts, found}:
      "[" ++ join(List.append(&2, String, texts, event.texts(unique(found, Nil{})))) ++ "]\n"

def abi(program: Core.Program, +backend: String, +entries: List<&2, String>) -> Result<&2, &2, String, String>:
  match program:
    case Core.Program{_, _, _, _, entry, _, _, _, +decls, _}:
      do Result<&2, &2, String, String>:
        leading : String <- Read.contract.first(entries, decls)
        prefix : String <- Read.prefix(decls, leading)
        +evm : String <- Certify.module(entry, prefix, backend)
        all : Items <- items(entries, evm, decls)
        return document(all)

def run(file: String, entries: List<String>) -> IO(Unit):
  do IO<Unit>:
    # host/run.js sets BEND_ENTRY to this file's real path.
    found : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_ENTRY")
    backend : String <- IO.pass(String, found)
    result : Result<&2, &2, String, Core.Program> <- Frontend.check(file)
    program : Core.Program <- Frontend.or_die(Core.Program, result)
    text : String <- Frontend.or_die(String, abi(program, backend, Certify.strings(entries)))
    IO.write(text)

def args(values: List<String>) -> IO(Unit):
  match values:
    case file <> entries:
      run(file, entries)
    case Nil{}:
      IO.die(Unit, 1, "Usage: abi.bend <contract.bend> <function>...")

def main() -> IO(Unit):
  do IO<Unit>:
    values : List<String> <- IO.args()
    args(values)
