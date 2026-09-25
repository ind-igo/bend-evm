import Base
import ../vendor/bend-frontend/src/core.bend as Core
import ./ir.bend as IR
import ./inline.bend as Inline
import ./keccak.bend as Keccak

# The reader turns a checked contract's Core terms into IR. It is untrusted:
# the generated certificate proves the IR equal to the contract, so a reader
# bug makes the certificate fail instead of miscompiling.
#
# A body is read one step at a time (cmd). A bound step (bind, step) is a
# word, an effect, or a call to one of the contract's own functions, which is
# inlined. The last step (last) is a branch, a pure result, a word, an effect
# or an inlined call. function reads a whole entry once, for every tool.

# Names
# -----

# s without the prefix p, if s starts with p.
def after(p: String, s: String) -> Maybe<&2, String>:
  match p s:
    case SNil{} rest:
      Some{rest}
    case SCon{x, xs} SCon{y, ys}:
      Bool.pick(Maybe<&2, String>, Char.is_eq(x, y), after(xs, ys), None{})
    case _ _:
      None{}

def reversed(value: Maybe<&2, String>) -> Maybe<&2, String>:
  match value:
    case Some{s}:
      Some{String.reverse(s)}
    case None{}:
      None{}

# s without the suffix p, if s ends with p.
def before(p: String, s: String) -> Maybe<&2, String>:
  reversed(after(String.reverse(p), String.reverse(s)))

def after_last.go(s: String, +c: Char) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+x, rest}:
      Bool.pick(String, Char.is_eq(x, c), "", SCon{x, after_last.go(rest, c)})

# The text after the last c in s, or all of s.
def after_last(+c: Char, s: String) -> String:
  String.reverse(after_last.go(String.reverse(s), c))

def canonical(found: Maybe<&2, String>, name: String) -> String:
  match found:
    case Some{rest}:
      "Evm." ++ rest
    case None{}:
      name

# Drop annotations and memos, and rename DSL references to "Evm.*" wherever
# the contract imported the module from.
def strip(+evm: String, term: Core.Term) -> Core.Term:
  match term:
    case Core.TAnn{value, _}:
      strip(evm, value)
    case Core.TVar{_, _, Some{value}}:
      strip(evm, value)
    case Core.TApp{func, arg}:
      f a = strip(evm, func) strip(evm, arg)
      Core.TApp{f, a}
    case Core.TLam{name, level, body, quantity}:
      Core.TLam{name, level, strip(evm, body), quantity}
    case Core.TRef{+name, parallel}:
      Core.TRef{canonical(after(evm, name), name), parallel}
    case other:
      other

# Calls
# -----

# A call's head, when the reader knows it. A string pattern costs the
# checker 33 splits per character, and a fallback case is copied into each
# split, so readers match on this tag, never on a name.
type Tag is Data:
  Sload{}
  Load{}
  Load2{}
  Caller{}
  Max{}
  Timestamp{}
  Chainid{}
  Self{}
  Keccak{}
  Typed{}
  Id{}
  Recover{}
  Select{}
  Add{}
  Sub{}
  Sstore{}
  Store{}
  Store2{}
  Require{}
  Emit{}
  IsEq{}
  IsLt{}
  Not{}
  NatType{}
  UnitType{}
  Bind{}
  Pure{}
  Branch{}
  Indexed{}
  EventType{}
  Unknown{}

type Named is Data:
  Named{name: String, tag: Tag}

def tags() -> List<&2, Named>:
  [Named{"Evm.sload", Sload{}},
  Named{"Evm.load", Load{}},
  Named{"Evm.load2", Load2{}},
  Named{"Evm.caller", Caller{}},
  Named{"Evm.max", Max{}},
  Named{"Evm.timestamp", Timestamp{}},
  Named{"Evm.chainid", Chainid{}},
  Named{"Evm.self", Self{}},
  Named{"Evm.keccak", Keccak{}},
  Named{"Evm.typed", Typed{}},
  Named{"Evm.id", Id{}},
  Named{"Evm.recover", Recover{}},
  Named{"Evm.select", Select{}},
  Named{"Evm.add", Add{}},
  Named{"Evm.sub", Sub{}},
  Named{"Evm.sstore", Sstore{}},
  Named{"Evm.store", Store{}},
  Named{"Evm.store2", Store2{}},
  Named{"Evm.require", Require{}},
  Named{"Evm.emit", Emit{}},
  Named{"Nat.is_eq", IsEq{}},
  Named{"Nat.is_lt", IsLt{}},
  Named{"Bool.not", Not{}},
  Named{"Nat", NatType{}},
  Named{"Unit", UnitType{}},
  Named{"Evm.Contract.bind", Bind{}},
  Named{"Evm.Contract.pure", Pure{}},
  Named{"Evm.branch", Branch{}},
  Named{"Evm.Indexed", Indexed{}},
  Named{"Evm.Event", EventType{}}]

def tag.go(table: List<&2, Named>, +name: String) -> Tag:
  match table:
    case Nil{}:
      Unknown{}
    case Named{n, t} <> rest:
      Bool.pick(Tag, String.eq(name, n), t, tag.go(rest, name))

def tag(+name: String) -> Tag:
  tag.go(tags(), name)

# An application spine: the referenced head, its tag and its arguments in
# order. Nested patterns over Term's many constructors make the checker's
# case trees explode, so readers match on Call instead.
type Call is Data:
  Call{tag: Tag, name: String, args: List<&2, Core.Term>}
  Other{}

def call(term: Core.Term, args: List<&2, Core.Term>) -> Call:
  match term:
    case Core.TApp{func, arg}:
      call(func, arg <> args)
    case Core.TRef{+name, _}:
      Call{tag(name), name, args}
    case _:
      Other{}

# Declarations
# ------------

# A safe, concrete definition: its arity, its type and its checked body.
type Def is Data:
  Def{arity: Nat, typ: Core.Term, body: Core.Term}

def definition(found: Maybe<&2, Core.Declaration>) -> Maybe<&2, Def>:
  match found:
    case Some{Core.Definition{Core.Header{_, _, arity, typ}, 0, False{}, Nil{}, _, Some{body}}}:
      Some{Def{U32.to_nat(arity), typ, body}}
    case _:
      None{}

def lookup(+decls: List<&2, Core.Declaration>, +name: String) -> Maybe<&2, Def>:
  definition(Core.find(decls, name))

type Param is Data:
  Param{name: String, domain: Core.Term}

# A def's parameters, from the first arity binders of its type, and its
# result type.
type Telescope is Data:
  Telescope{params: List<&2, Param>, result: Core.Term}

def telescope.push(p: Param, t: Telescope) -> Telescope:
  match t:
    case Telescope{params, result}:
      Telescope{p <> params, result}

def telescope.params(t: Telescope) -> List<&2, Param>:
  match t:
    case Telescope{params, _}:
      params

def telescope.result(t: Telescope) -> Core.Term:
  match t:
    case Telescope{_, result}:
      result

def telescope(arity: Nat, typ: Core.Term) -> Result<&2, &2, String, Telescope>:
  match arity typ:
    case n Core.TAnn{value, _}:
      telescope(n, value)
    case 0n result:
      Done{Telescope{Nil{}, Core.bare(result)}}
    case 1n+p Core.TAll{_, name, _, domain, body}:
      do Result<&2, &2, String, Telescope>:
        rest : Telescope <- telescope(p, body)
        return telescope.push(Param{name, domain}, rest)
    case _ _:
      Fail{"Expected one type per parameter"}

# ABI types
# ---------

type Abi is Data:
  Abi{name: String, abi: String}

def abi.go(table: List<&2, Abi>, +name: String) -> Result<&2, &2, String, String>:
  match table:
    case Nil{}:
      Fail{"Unsupported parameter type: " ++ name}
    case Abi{n, a} <> rest:
      Bool.pick(Result<&2, &2, String, String>, String.eq(name, n), Done{a}, abi.go(rest, name))

# The ABI type of a word: Nat is uint256, Evm.Address is address, and so on.
def abi(+name: String) -> Result<&2, &2, String, String>:
  abi.go([Abi{"Nat", "uint256"}, Abi{"Evm.Address", "address"}, Abi{"Evm.Uint8", "uint8"},
    Abi{"Evm.Boolean", "bool"}, Abi{"Evm.Bytes32", "bytes32"}], name)

def abi.term(+evm: String, typ: Core.Term) -> Result<&2, &2, String, String>:
  match typ:
    case Core.TAnn{value, _}:
      abi.term(evm, value)
    case Core.TRef{+name, _}:
      abi(canonical(after(evm, name), name))
    case _:
      Fail{"Unsupported parameter type"}

# The ABI type of a result, "" for Unit.
def result.name(+name: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, String.eq(name, "Unit"), Done{""}, abi(name))

def result.term(+evm: String, typ: Core.Term) -> Result<&2, &2, String, String>:
  match typ:
    case Core.TAnn{value, _}:
      result.term(evm, value)
    case Core.TRef{+name, _}:
      result.name(canonical(after(evm, name), name))
    case _:
      Fail{"Unsupported result type"}

# The A of an Evm.Contract(A) result.
def result.call(+evm: String, c: Call) -> Result<&2, &2, String, String>:
  match c:
    case Call{_, _, arg <> Nil{}}:
      result.term(evm, arg)
    case _:
      Fail{"Expected an Evm.Contract result"}

# Expressions
# -----------

def literal(value: Maybe<&2, Nat>) -> Result<&2, &2, String, IR.Expr>:
  match value:
    case Some{n}:
      Done{IR.Lit{n}}
    case None{}:
      Fail{"Invalid natural literal"}

def natural(value: Core.Literal) -> Result<&2, &2, String, IR.Expr>:
  match value:
    case Core.Natural{decimal}:
      literal(Nat.read(decimal))
    case _:
      Fail{"Only natural literals are words"}

def constant.body(term: Core.Term) -> Result<&2, &2, String, IR.Expr>:
  match term:
    case Core.TLit{value}:
      natural(value)
    case _:
      Fail{"Only literal constants can appear in expressions"}

# A reference to a zero-argument def whose body is a literal is that literal.
def constant(found: Maybe<&2, Def>) -> Result<&2, &2, String, IR.Expr>:
  match found:
    case Some{Def{0n, _, body}}:
      constant.body(Core.bare(body))
    case _:
      Fail{"Only literal constants can appear in expressions"}

def variable(level: Core.Level) -> Result<&2, &2, String, IR.Expr>:
  match level:
    case Core.Bound{value}:
      Done{IR.Var{U32.to_nat(value)}}
    case Core.Placeholder{}:
      Fail{"Unbound variable"}

def expr(term: Core.Term, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Expr>:
  match term:
    case Core.TAnn{value, _}:
      expr(value, decls)
    case Core.TLit{value}:
      natural(value)
    case Core.TVar{_, level, _}:
      variable(level)
    case Core.TRef{+name, _}:
      constant(lookup(decls, name))
    case _:
      Fail{"Unsupported expression"}

def terms(ts: List<&2, Core.Term>, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, List<&2, IR.Expr>>:
  match ts:
    case Nil{}:
      Done{Nil{}}
    case t <> rest:
      do Result<&2, &2, String, List<&2, IR.Expr>>:
        h : IR.Expr <- expr(t, decls)
        r : List<&2, IR.Expr> <- terms(rest, decls)
        return h <> r

# A list literal of expressions.
def exprs(term: Core.Term, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, List<&2, IR.Expr>>:
  match term:
    case Core.TAnn{value, _}:
      exprs(value, decls)
    case Core.TCtr{"Con", head <> tail <> Nil{}}:
      do Result<&2, &2, String, List<&2, IR.Expr>>:
        h : IR.Expr <- expr(head, decls)
        t : List<&2, IR.Expr> <- exprs(tail, decls)
        return h <> t
    case Core.TCtr{"Nil", Nil{}}:
      Done{Nil{}}
    case _:
      Fail{"Expected a list literal"}

# A plain slot, or a mapping entry under each key in turn.
def location.keys(keys: List<&2, Core.Term>, base: IR.Loc, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, IR.Loc>:
  match keys:
    case Nil{}:
      Done{base}
    case k <> rest:
      do Result<&2, &2, String, IR.Loc>:
        x : IR.Expr <- expr(k, decls)
        location.keys(rest, IR.Mapped{base, x}, decls)

def location(slot: Core.Term, keys: List<&2, Core.Term>, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, IR.Loc>:
  do Result<&2, &2, String, IR.Loc>:
    s : IR.Expr <- expr(slot, decls)
    location.keys(keys, IR.Plain{s}, decls)

# A text that keccak256 hashes, such as an EIP-712 type string: printable
# ASCII without quotes or backslashes, so the certificate can quote it, and
# one Keccak block, which the printer can hash.
def phrase.chars(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, rest}:
      +n = U32.to_nat(Char.to_u32(c))
      Bool.and(Bool.and(Bool.and(Nat.is_lt(31n, n), Nat.is_lt(n, 127n)), Bool.and(Bool.not(Nat.is_eq(n, 34n)),
        Bool.not(Nat.is_eq(n, 92n)))), phrase.chars(rest))

def phrase.check(+s: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, Bool.and(phrase.chars(s), Keccak.fits(s)),
    Done{s}, Fail{"A hashed text must be printable ASCII under 136 bytes, without quotes or backslashes"})

def phrase.literal(term: Core.Term) -> Result<&2, &2, String, String>:
  match term:
    case Core.TLit{Core.Text{value}}:
      phrase.check(value)
    case _:
      Fail{"Expected a text literal"}

def phrase.found(found: Maybe<&2, Def>) -> Result<&2, &2, String, String>:
  match found:
    case Some{Def{0n, _, body}}:
      phrase.literal(Core.bare(body))
    case _:
      Fail{"Expected a text literal"}

# A text literal, or a zero-argument def whose body is one.
def phrase(term: Core.Term, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, String>:
  match term:
    case Core.TAnn{value, _}:
      phrase(value, decls)
    case Core.TLit{value}:
      phrase.literal(Core.TLit{value})
    case Core.TRef{+name, _}:
      phrase.found(lookup(decls, name))
    case _:
      Fail{"Expected a text literal"}

# Conditions
# ----------

def cond.atom(c: Call, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Cond>:
  match c:
    case Call{IsEq{}, _, left <> right <> Nil{}}:
      do Result<&2, &2, String, IR.Cond>:
        l : IR.Expr <- expr(left, decls)
        r : IR.Expr <- expr(right, decls)
        return IR.Eq{l, r}
    case Call{IsLt{}, _, left <> right <> Nil{}}:
      do Result<&2, &2, String, IR.Cond>:
        l : IR.Expr <- expr(left, decls)
        r : IR.Expr <- expr(right, decls)
        return IR.Lt{l, r}
    case _:
      Fail{"Unsupported condition"}

def cond.go(+fuel: Nat, c: Call, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Cond>:
  match fuel c:
    case 1n+(+f) Call{Not{}, _, inner <> Nil{}}:
      do Result<&2, &2, String, IR.Cond>:
        x : IR.Cond <- cond.go(f, call(inner, Nil{}), decls)
        return IR.Not{x}
    case _ +other:
      cond.atom(other, decls)

# A condition: a comparison under at most 8 Bool.not.
def cond(test: Core.Term, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Cond>:
  cond.go(8n, call(test, Nil{}), decls)

# Words and effects
# -----------------

def word(c: Call, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Word>:
  match c:
    case Call{Sload{}, _, slot <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        l : IR.Loc <- location(slot, Nil{}, decls)
        return IR.SLoad{l}
    case Call{Load{}, _, slot <> key <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        l : IR.Loc <- location(slot, [key], decls)
        return IR.SLoad{l}
    case Call{Load2{}, _, slot <> outer <> inner <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        l : IR.Loc <- location(slot, [outer, inner], decls)
        return IR.SLoad{l}
    case Call{Caller{}, _, Nil{}}:
      Done{IR.Caller{}}
    case Call{Max{}, _, Nil{}}:
      Done{IR.Max{}}
    case Call{Timestamp{}, _, Nil{}}:
      Done{IR.Timestamp{}}
    case Call{Chainid{}, _, Nil{}}:
      Done{IR.ChainId{}}
    case Call{Self{}, _, Nil{}}:
      Done{IR.Self{}}
    case Call{Keccak{}, _, words <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        ws : List<&2, IR.Expr> <- exprs(words, decls)
        return IR.Keccak{ws}
    case Call{Typed{}, _, domain <> message <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        d : IR.Expr <- expr(domain, decls)
        m : IR.Expr <- expr(message, decls)
        return IR.Typed{d, m}
    case Call{Id{}, _, text <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        t : String <- phrase(text, decls)
        return IR.Id{t}
    case Call{Recover{}, _, digest <> v <> r <> s <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        d : IR.Expr <- expr(digest, decls)
        x : IR.Expr <- expr(v, decls)
        y : IR.Expr <- expr(r, decls)
        z : IR.Expr <- expr(s, decls)
        return IR.Recover{d, x, y, z}
    case Call{Select{}, _, test <> yes <> no <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        x : IR.Cond <- cond(test, decls)
        y : IR.Expr <- expr(yes, decls)
        n : IR.Expr <- expr(no, decls)
        return IR.Select{x, y, n}
    case Call{Add{}, _, left <> right <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        l : IR.Expr <- expr(left, decls)
        r : IR.Expr <- expr(right, decls)
        return IR.Add{l, r}
    case Call{Sub{}, _, left <> right <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        l : IR.Expr <- expr(left, decls)
        r : IR.Expr <- expr(right, decls)
        return IR.Sub{l, r}
    case _:
      Fail{"Unsupported word action"}

# Event signatures are printed into certificates and hashed into topic 0. An
# event's name must be an identifier, so the signature needs no quoting.
def identifier(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, rest}:
      Bool.and(Bool.or(Char.is_alpha(c), Bool.or(Char.is_digit(c), U32.is_eq(Char.to_u32(c), 95))), identifier(rest))

def joined(ts: List<&2, String>) -> String:
  match ts:
    case Nil{}:
      ""
    case t <> Nil{}:
      t
    case t <> rest:
      t ++ "," ++ joined(rest)

# An event field: whether it is Evm.Indexed, and its ABI type.
type Field is Data:
  Field{indexed: Bool, abi: String}

def field.of(+evm: String, c: Call, domain: Core.Term) -> Result<&2, &2, String, Field>:
  match c:
    case Call{Indexed{}, _, inner <> Nil{}}:
      do Result<&2, &2, String, Field>:
        t : String <- abi.term(evm, inner)
        return Field{True{}, t}
    case _:
      do Result<&2, &2, String, Field>:
        t : String <- abi.term(evm, domain)
        return Field{False{}, t}

def fields(+evm: String, params: List<&2, Param>) -> Result<&2, &2, String, List<&2, Field>>:
  match params:
    case Nil{}:
      Done{Nil{}}
    case Param{_, domain} <> rest:
      +d = strip(evm, domain)
      do Result<&2, &2, String, List<&2, Field>>:
        f : Field <- field.of(evm, call(d, Nil{}), d)
        fs : List<&2, Field> <- fields(evm, rest)
        return f <> fs

# An event's parameter types, then its indexed words and its data words.
type Parts is Data:
  Parts{types: List<&2, String>, topics: List<&2, IR.Expr>, data: List<&2, IR.Expr>}

def parts.put(+wrong: Bool, +indexed: Bool, t: String, x: IR.Expr, p: Parts) -> Result<&2, &2, String, Parts>:
  match wrong indexed p:
    case True{} _ _:
      Fail{"Indexed event fields must come before the others"}
    case False{} True{} Parts{types, topics, data}:
      Done{Parts{t <> types, x <> topics, data}}
    case False{} False{} Parts{types, topics, data}:
      Done{Parts{t <> types, topics, x <> data}}

def parts.add(+indexed: Bool, +late: Bool, t: String, e: Result<&2, &2, String, IR.Expr>,
  rest: Result<&2, &2, String, Parts>) -> Result<&2, &2, String, Parts>:
  do Result<&2, &2, String, Parts>:
    x : IR.Expr <- e
    p : Parts <- rest
    parts.put(Bool.and(indexed, late), indexed, t, x, p)

# late is true after the first field that is not indexed.
def parts(fs: List<&2, Field>, args: List<&2, Core.Term>, +late: Bool, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, Parts>:
  match fs args:
    case Nil{} Nil{}:
      Done{Parts{Nil{}, Nil{}, Nil{}}}
    case Field{+indexed, t} <> fr a <> ar:
      parts.add(indexed, late, t, expr(a, decls), parts(fr, ar, Bool.or(late, Bool.not(indexed)), decls))
    case _ _:
      Fail{"An event needs one argument for each field"}

# logN takes topic 0 and at most three indexed words.
def emit.log(+name: String, p: Parts) -> Result<&2, &2, String, IR.Effect>:
  match p:
    case Parts{types, +topics, data}:
      +signature = name ++ "(" ++ joined(types) ++ ")"
      Bool.pick(Result<&2, &2, String, IR.Effect>, Bool.and(identifier(name), Keccak.fits(signature)),
        Bool.pick(Result<&2, &2, String, IR.Effect>, Nat.is_lt(List.length(&2, IR.Expr, topics), 4n),
          Done{IR.Log{signature, topics, data}},
          Fail{"An event has at most three indexed words"}),
        Fail{signature ++ ": an event needs an identifier name and a signature under 136 bytes"})

def is_event(c: Call) -> Bool:
  match c:
    case Call{EventType{}, _, Nil{}}:
      True{}
    case _:
      False{}

def emit.event(+event: Bool, +evm: String, t: Telescope, +name: String, args: List<&2, Core.Term>,
  +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Effect>:
  match event t:
    case True{} Telescope{params, _}:
      do Result<&2, &2, String, IR.Effect>:
        fs : List<&2, Field> <- fields(evm, params)
        p : Parts <- parts(fs, args, False{}, decls)
        emit.log(after_last('.', name), p)
    case False{} _:
      Fail{"Evm.emit takes an event: a safe, concrete def whose result type is Evm.Event"}

def emit.found(+evm: String, found: Maybe<&2, Def>, +name: String, args: List<&2, Core.Term>,
  +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Effect>:
  match found:
    case Some{Def{arity, typ, _}}:
      do Result<&2, &2, String, IR.Effect>:
        +t : Telescope <- telescope(arity, typ)
        emit.event(is_event(call(strip(evm, telescope.result(t)), Nil{})), evm, t, name, args, decls)
    case None{}:
      Fail{"Evm.emit takes an event: a safe, concrete def whose result type is Evm.Event"}

# Evm.emit(Transfer(from, to, amount)): the signature and the topics come
# from the event def's name and parameter types. The reader does not read
# the def's body; the certificate proves it gives the same log. The ABI types
# are labels: a function must keep an address, uint8 or bool word in range.
def emit(+evm: String, c: Call, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Effect>:
  match c:
    case Call{_, +name, args}:
      emit.found(evm, lookup(decls, name), name, args, decls)
    case Other{}:
      Fail{"Evm.emit takes an event: a safe, concrete def whose result type is Evm.Event"}

def effect(c: Call, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Effect>:
  match c:
    case Call{Sstore{}, _, slot <> value <> Nil{}}:
      do Result<&2, &2, String, IR.Effect>:
        l : IR.Loc <- location(slot, Nil{}, decls)
        v : IR.Expr <- expr(value, decls)
        return IR.SStore{l, v}
    case Call{Store{}, _, slot <> key <> value <> Nil{}}:
      do Result<&2, &2, String, IR.Effect>:
        l : IR.Loc <- location(slot, [key], decls)
        v : IR.Expr <- expr(value, decls)
        return IR.SStore{l, v}
    case Call{Store2{}, _, slot <> outer <> inner <> value <> Nil{}}:
      do Result<&2, &2, String, IR.Effect>:
        l : IR.Loc <- location(slot, [outer, inner], decls)
        v : IR.Expr <- expr(value, decls)
        return IR.SStore{l, v}
    case Call{Require{}, _, condition <> Nil{}}:
      do Result<&2, &2, String, IR.Effect>:
        x : IR.Cond <- cond(condition, decls)
        return IR.Require{x}
    case Call{Emit{}, _, event <> Nil{}}:
      emit(evm, call(event, Nil{}), decls)
    case _:
      Fail{"Unsupported effect"}

# Steps
# -----

# The first result that is Done; otherwise both errors.
def first(own: Result<&2, &2, String, IR.Cmd>, called: Result<&2, &2, String, IR.Cmd>) -> Result<&2, &2, String, IR.Cmd>:
  match own called:
    case Done{value} _:
      Done{value}
    case Fail{_} Done{value}:
      Done{value}
    case Fail{e} Fail{f}:
      Fail{e ++ "; " ++ f}

def called.word(k: Result<&2, &2, String, Inline.Callee>, +level: Nat, +rest: IR.Cmd) -> Result<&2, &2, String, IR.Cmd>:
  do Result<&2, &2, String, IR.Cmd>:
    callee : Inline.Callee <- k
    body : IR.Cmd <- Inline.place(callee, Inline.max(level, Inline.top(rest)))
    Inline.splice.word(body, level, rest)

def called.unit(k: Result<&2, &2, String, Inline.Callee>, +level: Nat, +rest: IR.Cmd) -> Result<&2, &2, String, IR.Cmd>:
  do Result<&2, &2, String, IR.Cmd>:
    callee : Inline.Callee <- k
    body : IR.Cmd <- Inline.place(callee, Inline.max(level, Inline.top(rest)))
    Inline.splice.unit(body, rest)

def called.tail(k: Result<&2, &2, String, Inline.Callee>, +bound: Nat) -> Result<&2, &2, String, IR.Cmd>:
  do Result<&2, &2, String, IR.Cmd>:
    callee : Inline.Callee <- k
    Inline.place(callee, bound)

def own.word(w: Result<&2, &2, String, IR.Word>, +level: Nat, +rest: IR.Cmd) -> Result<&2, &2, String, IR.Cmd>:
  do Result<&2, &2, String, IR.Cmd>:
    value : IR.Word <- w
    return IR.Bind{value, level, rest}

def own.unit(e: Result<&2, &2, String, IR.Effect>, +rest: IR.Cmd) -> Result<&2, &2, String, IR.Cmd>:
  do Result<&2, &2, String, IR.Cmd>:
    value : IR.Effect <- e
    return IR.Then{value, rest}

# A bind over a word keeps its value; a bind over Unit is a plain step. The
# action is a DSL call, or else k, a call to one of the contract's functions.
def step(typ: Call, +action: Call, +level: Nat, rest: Result<&2, &2, String, IR.Cmd>,
  k: Result<&2, &2, String, Inline.Callee>, +evm: String, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, IR.Cmd>:
  match typ:
    case Call{NatType{}, _, Nil{}}:
      do Result<&2, &2, String, IR.Cmd>:
        +body : IR.Cmd <- rest
        first(own.word(word(action, decls), level, body), called.word(k, level, body))
    case Call{UnitType{}, _, Nil{}}:
      do Result<&2, &2, String, IR.Cmd>:
        +body : IR.Cmd <- rest
        first(own.unit(effect(action, evm, decls), body), called.unit(k, level, body))
    case _:
      Fail{"Only Nat and Unit results can be bound"}

def bind(c: Call, +level: Nat, rest: Result<&2, &2, String, IR.Cmd>, k: Result<&2, &2, String, Inline.Callee>,
  +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Cmd>:
  match c:
    case Call{Bind{}, _, typ <> _ <> action <> Nil{}}:
      step(call(typ, Nil{}), call(action, Nil{}), level, rest, k, evm, decls)
    case _:
      Fail{"Unsupported binding"}

# The action of a bind.
def action(c: Call) -> Call:
  match c:
    case Call{Bind{}, _, _ <> _ <> action <> Nil{}}:
      call(action, Nil{})
    case _:
      Other{}

def unit(term: Core.Term) -> Result<&2, &2, String, IR.Cmd>:
  match term:
    case Core.TCtr{"Unit", Nil{}}:
      Done{IR.Stop{}}
    case _:
      Fail{"Expected Unit{}"}

def pure(typ: Call, value: Core.Term, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Cmd>:
  match typ:
    case Call{NatType{}, _, Nil{}}:
      do Result<&2, &2, String, IR.Cmd>:
        v : IR.Expr <- expr(value, decls)
        return IR.Return{v}
    case Call{UnitType{}, _, Nil{}}:
      unit(value)
    case _:
      Fail{"Only Nat and Unit results can be returned"}

# A last step that is a word or an effect.
def last.own(w: Result<&2, &2, String, IR.Word>, e: Result<&2, &2, String, IR.Effect>) ->
  Result<&2, &2, String, IR.Cmd>:
  match w e:
    case Done{value} _:
      Done{IR.Tail{value}}
    case _ Done{value}:
      Done{IR.Finish{value}}
    case Fail{w} Fail{e}:
      Fail{"Unsupported contract step: " ++ w ++ "; " ++ e}

# A last step that is not a branch: a pure result, a word, an effect, or k.
def last.step(c: Call, k: Result<&2, &2, String, Inline.Callee>, +bound: Nat, +evm: String,
  +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Cmd>:
  match c:
    case Call{Pure{}, _, typ <> value <> Nil{}}:
      pure(call(typ, Nil{}), value, decls)
    case +other:
      first(last.own(word(other, decls), effect(other, evm, decls)), called.tail(k, bound))

# The last step. A branch reads both arms, each to the end of the call, with
# yes and no: two readers, because a closure can run only once.
def last(c: Call, yes: Core.Term -> Result<&2, &2, String, IR.Cmd>, no: Core.Term -> Result<&2, &2, String, IR.Cmd>,
  k: Result<&2, &2, String, Inline.Callee>, +bound: Nat, +evm: String, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, IR.Cmd>:
  match c:
    case Call{Branch{}, _, _ <> ok <> a <> b <> Nil{}}:
      do Result<&2, &2, String, IR.Cmd>:
        x : IR.Cond <- cond(ok, decls)
        y : IR.Cmd <- yes(a)
        n : IR.Cmd <- no(b)
        return IR.If{x, y, n}
    case +other:
      last.step(other, k, bound, evm, decls)

# Inlining
# --------

# A function's parameter levels and the body under its lambdas.
type Lambdas is Data:
  Lambdas{parameters: List<&2, Nat>, body: Core.Term}

def lambdas.prepend(level: Nat, rest: Lambdas) -> Lambdas:
  match rest:
    case Lambdas{parameters, body}:
      Lambdas{level <> parameters, body}

def lambdas(arity: Nat, term: Core.Term) -> Result<&2, &2, String, Lambdas>:
  match arity term:
    case 0n body:
      Done{Lambdas{Nil{}, body}}
    case 1n+p Core.TLam{_, Core.Bound{level}, body, _}:
      do Result<&2, &2, String, Lambdas>:
        rest : Lambdas <- lambdas(p, body)
        return lambdas.prepend(U32.to_nat(level), rest)
    case _ _:
      Fail{"Expected one lambda per parameter"}

def lambdas.found(found: Maybe<&2, Def>, +evm: String) -> Result<&2, &2, String, Lambdas>:
  match found:
    case Some{Def{arity, _, body}}:
      lambdas(arity, strip(evm, body))
    case None{}:
      Fail{"Expected a safe, concrete contract function"}

# The function that a call names, and its arguments.
type Target is Data:
  Target{parameters: List<&2, Nat>, body: Core.Term, args: List<&2, IR.Expr>}

def target.of(l: Lambdas, args: List<&2, IR.Expr>) -> Target:
  match l:
    case Lambdas{parameters, body}:
      Target{parameters, body, args}

# Only a call that is not a DSL call can be one of the contract's functions.
def target(c: Call, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, Target>:
  match c:
    case Call{Unknown{}, +name, args}:
      do Result<&2, &2, String, Target>:
        l : Lambdas <- lambdas.found(lookup(decls, name), evm)
        a : List<&2, IR.Expr> <- terms(args, decls)
        return target.of(l, a)
    case Call{Branch{}, _, _}:
      Fail{"A branch must be the last step of a function"}
    case _:
      Fail{"Not a call to a contract function"}

# The callee of a target, with its body read by read. A callee's parameters
# are levels 0 to arity - 1, so its locals start above them.
def callee(t: Result<&2, &2, String, Target>, read: Core.Term -> Nat -> Result<&2, &2, String, IR.Cmd>) ->
  Result<&2, &2, String, Inline.Callee>:
  match t:
    case Done{Target{+parameters, body, args}}:
      do Result<&2, &2, String, Inline.Callee>:
        b : IR.Cmd <- read(body, List.length(&2, Nat, parameters))
        return Inline.Callee{parameters, args, b}
    case Fail{e}:
      Fail{e}

def level(l: Core.Level) -> Nat:
  match l:
    case Core.Bound{value}:
      U32.to_nat(value)
    case Core.Placeholder{}:
      0n

# Inlined calls and branch arms nest at most this deep.
def depth() -> Nat:
  8n

# Reads a body. bound is the largest level declared so far. Each inlined
# call and each branch arm is read with less fuel, so reading ends.
def cmd(+fuel: Nat, term: Core.Term, +bound: Nat, +evm: String, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, IR.Cmd>:
  match fuel:
    case 0n:
      Fail{"Calls and branches nest more than 8 deep"}
    case 1n+p:
      match term:
        case Core.TApp{func, Core.TLam{_, l, body, _}}:
          +c = call(func, Nil{})
          +at = level(l)
          +k = callee(target(action(c), evm, decls), b => n => cmd(p, b, n, evm, decls))
          bind(c, at, cmd(fuel, body, at, evm, decls), k, evm, decls)
        case other:
          +c = call(other, Nil{})
          +k = callee(target(c, evm, decls), b => n => cmd(p, b, n, evm, decls))
          last(c, t => cmd(p, t, bound, evm, decls), t => cmd(p, t, bound, evm, decls), k, bound, evm, decls)

def output(c: IR.Cmd) -> IR.Output:
  match c:
    case IR.Bind{_, _, body}:
      output(body)
    case IR.Then{_, body}:
      output(body)
    case IR.Return{_}:
      IR.Returns{}
    case IR.Tail{_}:
      IR.Returns{}
    case IR.Finish{_}:
      IR.Stops{}
    case IR.Stop{}:
      IR.Stops{}
    case IR.If{_, yes, _}:
      output(yes)

# Entries
# -------

type Entry is Data:
  Entry{parameters: List<&2, Nat>, body: IR.Cmd}

# Parameter i must bind level i. A certificate then names each parameter
# once, and does not depend on how the reader numbered them.
def numbered(levels: List<&2, Nat>, +next: Nat) -> Bool:
  match levels:
    case Nil{}:
      True{}
    case level <> rest:
      Bool.and(Nat.is_eq(level, next), numbered(rest, Nat.add(next, 1n)))

def entry.checked(+name: String, +parameters: List<&2, Nat>, body: IR.Cmd) -> Result<&2, &2, String, Entry>:
  Bool.pick(Result<&2, &2, String, Entry>, numbered(parameters, 0n), Done{Entry{parameters, body}},
    Fail{name ++ ": parameter levels are not 0, 1, ..."})

def entry(+name: String, l: Lambdas, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, Entry>:
  match l:
    case Lambdas{+parameters, body}:
      do Result<&2, &2, String, Entry>:
        c : IR.Cmd <- cmd(depth(), body, List.length(&2, Nat, parameters), evm, decls)
        entry.checked(name, parameters, c)

# A parameter's name and ABI type.
type Input is Data:
  Input{name: String, abi: String}

def inputs(+evm: String, params: List<&2, Param>) -> Result<&2, &2, String, List<&2, Input>>:
  match params:
    case Nil{}:
      Done{Nil{}}
    case Param{name, domain} <> rest:
      do Result<&2, &2, String, List<&2, Input>>:
        t : String <- abi.term(evm, domain)
        r : List<&2, Input> <- inputs(evm, rest)
        return Input{name, t} <> r

# An entry, read once for every tool: a constant string such as an ERC-20's
# name(), which the printer returns ABI-encoded and which has nothing to
# certify, or a contract function with its inputs, the ABI type of its
# result ("" for Unit) and its IR.
type Function is Data:
  Constant{name: String, text: String}
  Contract{name: String, inputs: List<&2, Input>, result: String, entry: Entry}

def text(term: Core.Term) -> Maybe<&2, String>:
  match term:
    case Core.TLit{Core.Text{value}}:
      Some{value}
    case _:
      None{}

# The text of a zero-argument def whose body is a text literal.
def constant.text(found: Maybe<&2, Def>) -> Maybe<&2, String>:
  match found:
    case Some{Def{0n, _, body}}:
      text(Core.bare(body))
    case _:
      None{}

def contract(+name: String, d: Def, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, Function>:
  match d:
    case Def{+arity, typ, body}:
      do Result<&2, &2, String, Function>:
        +t : Telescope <- telescope(arity, typ)
        ins : List<&2, Input> <- inputs(evm, telescope.params(t))
        out : String <- result.call(evm, call(telescope.result(t), Nil{}))
        l : Lambdas <- lambdas(arity, strip(evm, body))
        e : Entry <- entry(name, l, evm, decls)
        return Contract{name, ins, out, e}

def function.found(+name: String, text: Maybe<&2, String>, found: Maybe<&2, Def>, +evm: String,
  +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, Function>:
  match text found:
    case Some{value} _:
      Done{Constant{name, value}}
    case None{} Some{d}:
      contract(name, d, evm, decls)
    case None{} None{}:
      Fail{"Unknown contract function: " ++ name}

def function(+evm: String, +decls: List<&2, Core.Declaration>, +name: String) -> Result<&2, &2, String, Function>:
  +found = lookup(decls, name)
  function.found(name, constant.text(found), found, evm, decls)

def functions(+evm: String, +decls: List<&2, Core.Declaration>, names: List<&2, String>) ->
  Result<&2, &2, String, List<&2, Function>>:
  match names:
    case Nil{}:
      Done{Nil{}}
    case +name <> rest:
      do Result<&2, &2, String, List<&2, Function>>:
        f : Function <- function(evm, decls, name)
        fs : List<&2, Function> <- functions(evm, decls, rest)
        return f <> fs

# The Evm module
# --------------

def module.found(found: Maybe<&2, String>) -> Result<&2, &2, String, String>:
  match found:
    case Some{prefix}:
      Done{prefix ++ "."}
    case None{}:
      Fail{"Expected an Evm.Contract result"}

def module.name(c: Call) -> Result<&2, &2, String, String>:
  match c:
    case Call{_, name, _}:
      module.found(before(".Contract", name))
    case Other{}:
      Fail{"Expected an Evm.Contract result"}

def module.of(+name: String, found: Maybe<&2, Def>) -> Result<&2, &2, String, String>:
  match found:
    case Some{Def{arity, typ, _}}:
      do Result<&2, &2, String, String>:
        t : Telescope <- telescope(arity, typ)
        module.name(call(telescope.result(t), Nil{}))
    case None{}:
      Fail{"Unknown contract function: " ++ name}

# The Evm module's name prefix, such as "../Evm.", from the result type of
# the first entry that is not a constant string.
def module(+decls: List<&2, Core.Declaration>, names: List<&2, String>) -> Result<&2, &2, String, String>:
  match names:
    case Nil{}:
      Fail{"Name at least one contract function"}
    case +name <> rest:
      +found = lookup(decls, name)
      Bool.pick(Result<&2, &2, String, String>, Maybe.is_some(&2, String, constant.text(found)), module(decls, rest),
        module.of(name, found))
