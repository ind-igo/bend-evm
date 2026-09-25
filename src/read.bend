import Base
import ../vendor/bend-frontend/src/core.bend as Core
import ./ir.bend as IR
import ./inline.bend as Inline

# The reader proposes IR and the generated certificate proves it. A reader bug
# makes the certificate fail instead of miscompiling, so the reader is untrusted.

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

def canonical(found: Maybe<&2, String>, name: String) -> String:
  match found:
    case Some{rest}:
      "Evm." ++ rest
    case None{}:
      name

# Drop annotations and memos, and rename DSL references to "Evm.*" wherever
# the contract imported the module from. Later patterns can then nest.
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

# An application spine: the referenced head and its arguments in order.
# Readers match names on Call, never deep inside Term: nested patterns over
# Term's many constructors make the checker's case trees explode.
# A call's head, when the reader knows it. A string pattern costs the
# checker 33 splits per character, and a fallback case is copied into each
# split, so readers match on the tag instead.
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
  Log{}
  Require{}
  IsEq{}
  IsLt{}
  Not{}
  NatType{}
  UnitType{}
  Bind{}
  Pure{}
  Branch{}
  Emit{}
  Indexed{}
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
  Named{"Evm.log", Log{}},
  Named{"Evm.require", Require{}},
  Named{"Nat.is_eq", IsEq{}},
  Named{"Nat.is_lt", IsLt{}},
  Named{"Bool.not", Not{}},
  Named{"Nat", NatType{}},
  Named{"Unit", UnitType{}},
  Named{"Evm.Contract.bind", Bind{}},
  Named{"Evm.Contract.pure", Pure{}},
  Named{"Evm.branch", Branch{}},
  Named{"Evm.emit", Emit{}},
  Named{"Evm.Indexed", Indexed{}}]

def tag.go(table: List<&2, Named>, +name: String) -> Tag:
  match table:
    case Nil{}:
      Unknown{}
    case Named{n, t} <> rest:
      Bool.pick(Tag, String.eq(name, n), t, tag.go(rest, name))

def tag(+name: String) -> Tag:
  tag.go(tags(), name)

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
def constant(found: Maybe<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Expr>:
  match found:
    case Some{Core.Definition{Core.Header{_, _, 0, _}, 0, False{}, Nil{}, _, Some{body}}}:
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
      constant(Core.find(decls, name))
    case _:
      Fail{"Unsupported expression"}

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

# Event signatures are printed into certificates and hashed into topic 0, so
# they may only hold ABI signature characters and must fit one Keccak block.
def signature.char(+c: Char) -> Bool:
  +n = Char.to_u32(c)
  Bool.or(Char.is_alpha(c), Bool.or(Char.is_digit(c), Bool.or(U32.is_eq(n, 95), Bool.or(U32.is_eq(n, 40),
    Bool.or(U32.is_eq(n, 41), Bool.or(U32.is_eq(n, 44), Bool.or(U32.is_eq(n, 91), U32.is_eq(n, 93))))))))

def signature.chars(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, rest}:
      Bool.and(signature.char(c), signature.chars(rest))

def signature(+s: String) -> Result<&2, &2, String, String>:
  Bool.pick(Result<&2, &2, String, String>, Bool.and(signature.chars(s), Nat.is_lt(String.length(s), 136n)),
    Done{s}, Fail{"Event signatures must be ABI signatures under 136 bytes"})

def text.body(term: Core.Term) -> Result<&2, &2, String, String>:
  match term:
    case Core.TLit{Core.Text{value}}:
      signature(value)
    case _:
      Fail{"Expected an event signature literal"}

def text.found(found: Maybe<&2, Core.Declaration>) -> Result<&2, &2, String, String>:
  match found:
    case Some{Core.Definition{Core.Header{_, _, 0, _}, 0, False{}, Nil{}, _, Some{body}}}:
      text.body(Core.bare(body))
    case _:
      Fail{"Expected an event signature literal"}

# An event signature: a text literal, or a zero-argument def whose body is one.
def text(term: Core.Term, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, String>:
  match term:
    case Core.TAnn{value, _}:
      text(value, decls)
    case Core.TLit{Core.Text{value}}:
      signature(value)
    case Core.TRef{+name, _}:
      text.found(Core.find(decls, name))
    case _:
      Fail{"Expected an event signature literal"}

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
  Bool.pick(Result<&2, &2, String, String>, Bool.and(phrase.chars(s), Nat.is_lt(String.length(s), 136n)),
    Done{s}, Fail{"A hashed text must be printable ASCII under 136 bytes, without quotes or backslashes"})

def phrase.body(term: Core.Term) -> Result<&2, &2, String, String>:
  match term:
    case Core.TLit{Core.Text{value}}:
      phrase.check(value)
    case _:
      Fail{"Expected a text literal"}

def phrase.found(found: Maybe<&2, Core.Declaration>) -> Result<&2, &2, String, String>:
  match found:
    case Some{Core.Definition{Core.Header{_, _, 0, _}, 0, False{}, Nil{}, _, Some{body}}}:
      phrase.body(Core.bare(body))
    case _:
      Fail{"Expected a text literal"}

def phrase(term: Core.Term, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, String>:
  match term:
    case Core.TAnn{value, _}:
      phrase(value, decls)
    case Core.TLit{Core.Text{value}}:
      phrase.check(value)
    case Core.TRef{+name, _}:
      phrase.found(Core.find(decls, name))
    case _:
      Fail{"Expected a text literal"}

def commas(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{c, rest}:
      Nat.add(Bool.pick(Nat, U32.is_eq(Char.to_u32(c), 44), 1n, 0n), commas(rest))

def closes(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, _}:
      U32.is_eq(Char.to_u32(c), 41)

# True when the signature has "()", that is no parameters.
def bare(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, +rest}:
      Bool.pick(Bool, U32.is_eq(Char.to_u32(c), 40), closes(rest), bare(rest))

# Each parameter is one word: its commas plus one, or none for "()". A tuple
# or array parameter counts wrong here, so such events fail the check.
def parameters(+s: String) -> Nat:
  Bool.pick(Nat, bare(s), 0n, Nat.add(1n, commas(s)))

# logN takes topic 0 and at most three indexed words, and the indexed and
# data words together are the signature's parameters.
def log(+event: String, +topics: List<&2, IR.Expr>, +data: List<&2, IR.Expr>) -> Result<&2, &2, String, IR.Effect>:
  +words = Nat.add(List.length(&2, IR.Expr, topics), List.length(&2, IR.Expr, data))
  Bool.pick(Result<&2, &2, String, IR.Effect>, Nat.is_lt(List.length(&2, IR.Expr, topics), 4n),
    Bool.pick(Result<&2, &2, String, IR.Effect>, Nat.is_eq(words, parameters(event)),
      Done{IR.Log{event, topics, data}},
      Fail{"An event needs one word for each parameter of its signature"}),
    Fail{"An event has at most three indexed words"})

type Operands is Data:
  Operands{left: IR.Expr, right: IR.Expr}

def operands(left: Core.Term, right: Core.Term, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, Operands>:
  do Result<&2, &2, String, Operands>:
    l : IR.Expr <- expr(left, decls)
    r : IR.Expr <- expr(right, decls)
    return Operands{l, r}

def eq(pair: Operands) -> IR.Cond:
  match pair:
    case Operands{l, r}:
      IR.Eq{l, r}

def lt(pair: Operands) -> IR.Cond:
  match pair:
    case Operands{l, r}:
      IR.Lt{l, r}

def add(pair: Operands) -> IR.Word:
  match pair:
    case Operands{l, r}:
      IR.Add{l, r}

def sub(pair: Operands) -> IR.Word:
  match pair:
    case Operands{l, r}:
      IR.Sub{l, r}

def select(c: IR.Cond, pair: Operands) -> IR.Word:
  match pair:
    case Operands{y, n}:
      IR.Select{c, y, n}

def typed(pair: Operands) -> IR.Word:
  match pair:
    case Operands{d, m}:
      IR.Typed{d, m}

def recover(first: Operands, second: Operands) -> IR.Word:
  match first second:
    case Operands{d, v} Operands{r, s}:
      IR.Recover{d, v, r, s}

def mapped(pair: Operands) -> IR.Loc:
  match pair:
    case Operands{s, k}:
      IR.Mapped{IR.Plain{s}, k}

def cond(c: Call, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Cond>:
  match c:
    case Call{IsEq{}, _, left <> right <> Nil{}}:
      do Result<&2, &2, String, IR.Cond>:
        pair : Operands <- operands(left, right, decls)
        return eq(pair)
    case Call{IsLt{}, _, left <> right <> Nil{}}:
      do Result<&2, &2, String, IR.Cond>:
        pair : Operands <- operands(left, right, decls)
        return lt(pair)
    case _:
      Fail{"Unsupported condition"}

def negate(c: IR.Cond) -> IR.Cond:
  IR.Not{c}

# Conditions nest through Bool.not, at most fuel deep.
def cond.go(+fuel: Nat, c: Call, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Cond>:
  match fuel c:
    case 1n+(+f) Call{Not{}, _, inner <> Nil{}}:
      do Result<&2, &2, String, IR.Cond>:
        x : IR.Cond <- cond.go(f, call(inner, Nil{}), decls)
        return negate(x)
    case _ +other:
      cond(other, decls)

def word(c: Call, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Word>:
  match c:
    case Call{Sload{}, _, slot <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        s : IR.Expr <- expr(slot, decls)
        return IR.SLoad{IR.Plain{s}}
    case Call{Load{}, _, slot <> key <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        pair : Operands <- operands(slot, key, decls)
        return IR.SLoad{mapped(pair)}
    case Call{Load2{}, _, slot <> outer <> inner <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        pair : Operands <- operands(slot, outer, decls)
        k : IR.Expr <- expr(inner, decls)
        return IR.SLoad{IR.Mapped{mapped(pair), k}}
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
        pair : Operands <- operands(domain, message, decls)
        return typed(pair)
    case Call{Id{}, _, text <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        t : String <- phrase(text, decls)
        return IR.Id{t}
    case Call{Recover{}, _, digest <> v <> r <> s <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        first : Operands <- operands(digest, v, decls)
        second : Operands <- operands(r, s, decls)
        return recover(first, second)
    case Call{Select{}, _, test <> yes <> no <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        c : IR.Cond <- cond.go(8n, call(test, Nil{}), decls)
        pair : Operands <- operands(yes, no, decls)
        return select(c, pair)
    case Call{Add{}, _, left <> right <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        pair : Operands <- operands(left, right, decls)
        return add(pair)
    case Call{Sub{}, _, left <> right <> Nil{}}:
      do Result<&2, &2, String, IR.Word>:
        pair : Operands <- operands(left, right, decls)
        return sub(pair)
    case _:
      Fail{"Unsupported word action"}

# The ABI type of a parameter: Nat is uint256, Evm.Address is address.
type Abi is Data:
  Abi{name: String, abi: String}

def abi.go(table: List<&2, Abi>, +name: String) -> Result<&2, &2, String, String>:
  match table:
    case Nil{}:
      Fail{"Unsupported parameter type: " ++ name}
    case Abi{n, a} <> rest:
      Bool.pick(Result<&2, &2, String, String>, String.eq(name, n), Done{a}, abi.go(rest, name))

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

# The text after the last dot of a name: an event constructor's own name.
def short.go(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, rest}:
      Bool.pick(String, Char.is_eq(c, '.'), "", SCon{c, short.go(rest)})

def short(name: String) -> String:
  String.reverse(short.go(String.reverse(name)))

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

def field(+evm: String, +domain: Core.Term) -> Result<&2, &2, String, Field>:
  field.of(evm, call(domain, Nil{}), domain)

def fields(+evm: String, typ: Core.Term) -> Result<&2, &2, String, List<&2, Field>>:
  match typ:
    case Core.TAll{_, _, _, domain, body}:
      do Result<&2, &2, String, List<&2, Field>>:
        f : Field <- field(evm, strip(evm, domain))
        rest : List<&2, Field> <- fields(evm, body)
        return f <> rest
    case _:
      Done{Nil{}}

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
      Fail{"An event constructor needs one argument for each field"}

def emit.log(name: String, p: Parts) -> Result<&2, &2, String, IR.Effect>:
  match p:
    case Parts{types, topics, data}:
      do Result<&2, &2, String, IR.Effect>:
        +event : String <- signature(short(name) ++ "(" ++ joined(types) ++ ")")
        log(event, topics, data)

def constructor.in(cs: List<&2, Core.Constructor>, +wanted: String) -> Maybe<&2, Core.Constructor>:
  match cs:
    case Nil{}:
      None{}
    case Core.Constructor{+name, +arity, +typ} <> rest:
      Bool.pick(Maybe<&2, Core.Constructor>, String.eq(name, wanted), Some{Core.Constructor{name, arity, typ}},
        constructor.in(rest, wanted))

def constructor.of(d: Core.Declaration, +wanted: String) -> Maybe<&2, Core.Constructor>:
  match d:
    case Core.Algebraic{_, _, _, cs}:
      constructor.in(cs, wanted)
    case _:
      None{}

def constructor.or(found: Maybe<&2, Core.Constructor>, rest: Maybe<&2, Core.Constructor>) -> Maybe<&2, Core.Constructor>:
  match found:
    case Some{c}:
      Some{c}
    case None{}:
      rest

# The declared constructor named wanted.
def constructor(decls: List<&2, Core.Declaration>, +wanted: String) -> Maybe<&2, Core.Constructor>:
  match decls:
    case Nil{}:
      None{}
    case d <> rest:
      constructor.or(constructor.of(d, wanted), constructor(rest, wanted))

def emit.found(+evm: String, found: Maybe<&2, Core.Constructor>, +name: String, args: List<&2, Core.Term>,
  +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Effect>:
  match found:
    case Some{Core.Constructor{_, _, typ}}:
      do Result<&2, &2, String, IR.Effect>:
        fs : List<&2, Field> <- fields(evm, typ)
        p : Parts <- parts(fs, args, False{}, decls)
        emit.log(name, p)
    case None{}:
      Fail{"Unknown event constructor: " ++ name}

def emit.value(+evm: String, term: Core.Term, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Effect>:
  match term:
    case Core.TAnn{value, _}:
      emit.value(evm, value, decls)
    case Core.TCtr{+name, args}:
      emit.found(evm, constructor(decls, name), name, args, decls)
    case _:
      Fail{"Evm.emit takes an encoder applied to an event constructor"}

# Evm.emit(encode(Event{...})): the signature and the topics come from the
# constructor's field types. The certificate checks that encode agrees.
def emit(+evm: String, c: Call, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Effect>:
  match c:
    case Call{_, _, value <> Nil{}}:
      emit.value(evm, value, decls)
    case _:
      Fail{"Evm.emit takes an encoder applied to an event constructor"}

def effect(c: Call, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, IR.Effect>:
  match c:
    case Call{Sstore{}, _, slot <> value <> Nil{}}:
      do Result<&2, &2, String, IR.Effect>:
        s : IR.Expr <- expr(slot, decls)
        v : IR.Expr <- expr(value, decls)
        return IR.SStore{IR.Plain{s}, v}
    case Call{Store{}, _, slot <> key <> value <> Nil{}}:
      do Result<&2, &2, String, IR.Effect>:
        pair : Operands <- operands(slot, key, decls)
        v : IR.Expr <- expr(value, decls)
        return IR.SStore{mapped(pair), v}
    case Call{Store2{}, _, slot <> outer <> inner <> value <> Nil{}}:
      do Result<&2, &2, String, IR.Effect>:
        pair : Operands <- operands(slot, outer, decls)
        k : IR.Expr <- expr(inner, decls)
        v : IR.Expr <- expr(value, decls)
        return IR.SStore{IR.Mapped{mapped(pair), k}, v}
    case Call{Log{}, _, event <> topics <> data <> Nil{}}:
      do Result<&2, &2, String, IR.Effect>:
        e : String <- text(event, decls)
        t : List<&2, IR.Expr> <- exprs(topics, decls)
        d : List<&2, IR.Expr> <- exprs(data, decls)
        log(e, t, d)
    case Call{Require{}, _, condition <> Nil{}}:
      do Result<&2, &2, String, IR.Effect>:
        c : IR.Cond <- cond.go(8n, call(condition, Nil{}), decls)
        return IR.Require{c}
    case Call{Emit{}, _, event <> Nil{}}:
      emit(evm, call(event, Nil{}), decls)
    case _:
      Fail{"Unsupported effect"}

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

def own.word(w: Result<&2, &2, String, IR.Word>, +level: Nat, +rest: IR.Cmd) -> Result<&2, &2, String, IR.Cmd>:
  do Result<&2, &2, String, IR.Cmd>:
    value : IR.Word <- w
    return IR.Bind{value, level, rest}

def own.unit(e: Result<&2, &2, String, IR.Effect>, +rest: IR.Cmd) -> Result<&2, &2, String, IR.Cmd>:
  do Result<&2, &2, String, IR.Cmd>:
    value : IR.Effect <- e
    return IR.Then{value, rest}

# A bind over a word keeps its value; a bind over Unit is a plain step. The
# action is a DSL call, or else a call to one of the contract's functions.
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

def last(w: Result<&2, &2, String, IR.Word>, e: Result<&2, &2, String, IR.Effect>) ->
  Result<&2, &2, String, IR.Cmd>:
  match w e:
    case Done{value} _:
      Done{IR.Tail{value}}
    case _ Done{value}:
      Done{IR.Finish{value}}
    case Fail{w} Fail{e}:
      Fail{"Unsupported contract step: " ++ w ++ "; " ++ e}

def called.tail(k: Result<&2, &2, String, Inline.Callee>, +bound: Nat) -> Result<&2, &2, String, IR.Cmd>:
  do Result<&2, &2, String, IR.Cmd>:
    callee : Inline.Callee <- k
    Inline.place(callee, bound)

def branch(c: IR.Cond, yes: IR.Cmd, no: IR.Cmd) -> IR.Cmd:
  IR.If{c, yes, no}

def final(c: Call, k: Result<&2, &2, String, Inline.Callee>, +bound: Nat, +evm: String, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, IR.Cmd>:
  match c:
    case Call{Pure{}, _, typ <> value <> Nil{}}:
      pure(call(typ, Nil{}), value, decls)
    case +other:
      first(last(word(other, decls), effect(other, evm, decls)), called.tail(k, bound))

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

def lambdas.found(found: Maybe<&2, Core.Declaration>, +evm: String) -> Result<&2, &2, String, Lambdas>:
  match found:
    case Some{Core.Definition{Core.Header{_, _, +arity, _}, 0, False{}, Nil{}, _, Some{body}}}:
      lambdas(U32.to_nat(arity), strip(evm, body))
    case _:
      Fail{"Expected a safe, concrete contract function"}

def lambdas.parameters(l: Lambdas) -> List<&2, Nat>:
  match l:
    case Lambdas{parameters, _}:
      parameters

def lambdas.body(l: Lambdas) -> Core.Term:
  match l:
    case Lambdas{_, body}:
      body

def terms(ts: List<&2, Core.Term>, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, List<&2, IR.Expr>>:
  match ts:
    case Nil{}:
      Done{Nil{}}
    case t <> rest:
      do Result<&2, &2, String, List<&2, IR.Expr>>:
        h : IR.Expr <- expr(t, decls)
        r : List<&2, IR.Expr> <- terms(rest, decls)
        return h <> r

# The function that a call names, and its arguments.
type Target is Data:
  Target{lambdas: Lambdas, args: List<&2, IR.Expr>}

def target(c: Call, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, Target>:
  match c:
    case Call{Branch{}, _, _}:
      Fail{"A branch must be the last step of a function"}
    case Call{_, name, args}:
      do Result<&2, &2, String, Target>:
        l : Lambdas <- lambdas.found(Core.find(decls, name), evm)
        a : List<&2, IR.Expr> <- terms(args, decls)
        return Target{l, a}
    case Other{}:
      Fail{"Unsupported call"}

def target.body(t: Target) -> Core.Term:
  match t:
    case Target{l, _}:
      lambdas.body(l)

# A callee's parameters are levels 0 to arity - 1, so its locals start above.
def target.arity(t: Target) -> Nat:
  match t:
    case Target{l, _}:
      List.length(&2, Nat, lambdas.parameters(l))

def target.callee(t: Target, body: IR.Cmd) -> Inline.Callee:
  match t:
    case Target{l, args}:
      Inline.Callee{lambdas.parameters(l), args, body}

def action(c: Call) -> Call:
  match c:
    case Call{Bind{}, _, _ <> _ <> action <> Nil{}}:
      call(action, Nil{})
    case _:
      Other{}

def level(l: Core.Level) -> Nat:
  match l:
    case Core.Bound{value}:
      U32.to_nat(value)
    case Core.Placeholder{}:
      0n

# A final Evm.branch reads both arms, each to the end of the call; any other
# final step is a word, an effect or a call. yes and no read the arms.
def tail(c: Call, yes: Core.Term -> Result<&2, &2, String, IR.Cmd>, no: Core.Term -> Result<&2, &2, String, IR.Cmd>,
  k: Result<&2, &2, String, Inline.Callee>, +bound: Nat, +evm: String, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, IR.Cmd>:
  match c:
    case Call{Branch{}, _, ok <> _ <> a <> b <> Nil{}}:
      do Result<&2, &2, String, IR.Cmd>:
        x : IR.Cond <- cond.go(8n, call(ok, Nil{}), decls)
        y : IR.Cmd <- yes(a)
        n : IR.Cmd <- no(b)
        return branch(x, y, n)
    case +other:
      final(other, k, bound, evm, decls)

# Calls to the contract's own functions are inlined, at most this deep.
def depth() -> Nat:
  8n

# Reads a body. bound is the largest level declared so far. Each inlined
# call reads its callee with less fuel, so reading ends.
def cmd(+fuel: Nat, term: Core.Term, +bound: Nat, +evm: String, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, IR.Cmd>:
  match fuel:
    case 0n:
      Fail{"Calls nest too deep"}
    case 1n+p:
      match term:
        case Core.TApp{func, Core.TLam{_, l, body, _}}:
          +c = call(func, Nil{})
          +at = level(l)
          +t = target(action(c), evm, decls)
          +k = do Result<&2, &2, String, Inline.Callee>:
            +x : Target <- t
            b : IR.Cmd <- cmd(p, target.body(x), target.arity(x), evm, decls)
            return target.callee(x, b)
          bind(c, at, cmd(fuel, body, at, evm, decls), k, evm, decls)
        case other:
          +c = call(other, Nil{})
          +k = do Result<&2, &2, String, Inline.Callee>:
            +x : Target <- target(c, evm, decls)
            b : IR.Cmd <- cmd(p, target.body(x), target.arity(x), evm, decls)
            return target.callee(x, b)
          tail(c, t => cmd(p, t, bound, evm, decls), t => cmd(p, t, bound, evm, decls), k, bound, evm, decls)

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

type Entry is Data:
  Entry{parameters: List<&2, Nat>, body: IR.Cmd}

# Parameters are the leading lambdas; the certificate checks their types.
def entry.read(l: Lambdas, +arity: Nat, +evm: String, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, Entry>:
  match l:
    case Lambdas{parameters, body}:
      do Result<&2, &2, String, Entry>:
        c : IR.Cmd <- cmd(depth(), body, arity, evm, decls)
        return Entry{parameters, c}

def module.found(found: Maybe<&2, String>) -> Result<&2, &2, String, String>:
  match found:
    case Some{prefix}:
      Done{prefix}
    case None{}:
      Fail{"Expected an Evm.Contract result"}

def module.call(c: Call) -> Result<&2, &2, String, String>:
  match c:
    case Call{_, name, _}:
      module.found(before("Contract", name))
    case Other{}:
      Fail{"Expected an Evm.Contract result"}

# The Evm module's name prefix, such as "../Evm.", from the entry's result type.
def module(arity: Nat, typ: Core.Term) -> Result<&2, &2, String, String>:
  match arity typ:
    case n Core.TAnn{value, _}:
      module(n, value)
    case 0n result:
      module.call(call(result, Nil{}))
    case 1n+p Core.TAll{_, _, _, _, body}:
      module(p, body)
    case _ _:
      Fail{"Expected an Evm.Contract result"}

def entry.found(found: Maybe<&2, Core.Declaration>, +evm: String, +decls: List<&2, Core.Declaration>) ->
  Result<&2, &2, String, Entry>:
  match found:
    case Some{Core.Definition{Core.Header{_, _, +arity, _}, 0, False{}, Nil{}, _, Some{body}}}:
      do Result<&2, &2, String, Entry>:
        l : Lambdas <- lambdas(U32.to_nat(arity), strip(evm, body))
        entry.read(l, U32.to_nat(arity), evm, decls)
    case _:
      Fail{"Expected a safe, concrete contract function"}

def entry(+evm: String, +decls: List<&2, Core.Declaration>, name: String) -> Result<&2, &2, String, Entry>:
  entry.found(Core.find(decls, name), evm, decls)

def types.go(arity: Nat, +evm: String, typ: Core.Term) -> Result<&2, &2, String, List<&2, String>>:
  match arity typ:
    case n Core.TAnn{value, _}:
      types.go(n, evm, value)
    case 0n _:
      Done{Nil{}}
    case 1n+p Core.TAll{_, _, _, domain, body}:
      do Result<&2, &2, String, List<&2, String>>:
        t : String <- abi.term(evm, domain)
        rest : List<&2, String> <- types.go(p, evm, body)
        return t <> rest
    case _ _:
      Fail{"Expected one type per parameter"}

def types.found(found: Maybe<&2, Core.Declaration>, +evm: String) -> Result<&2, &2, String, List<&2, String>>:
  match found:
    case Some{Core.Definition{Core.Header{_, _, arity, typ}, _, _, _, _, _}}:
      types.go(U32.to_nat(arity), evm, typ)
    case _:
      Fail{"Unknown contract function"}

# The ABI types of a contract function's parameters, in order.
def types(+evm: String, +decls: List<&2, Core.Declaration>, name: String) -> Result<&2, &2, String, List<&2, String>>:
  types.found(Core.find(decls, name), evm)

def prefix.found(found: Maybe<&2, Core.Declaration>) -> Result<&2, &2, String, String>:
  match found:
    case Some{Core.Definition{Core.Header{_, _, arity, typ}, _, _, _, _, _}}:
      module(U32.to_nat(arity), typ)
    case _:
      Fail{"Unknown contract function"}

def prefix(+decls: List<&2, Core.Declaration>, name: String) -> Result<&2, &2, String, String>:
  prefix.found(Core.find(decls, name))

# A constant string entry, such as an ERC-20's name(): a definition with no
# parameters whose body is a string literal. It is not a contract, so there
# is nothing to certify, and the printer returns it ABI-encoded.
def string_entry.term(term: Core.Term) -> Maybe<&2, String>:
  match term:
    case Core.TAnn{value, _}:
      string_entry.term(value)
    case Core.TLit{Core.Text{value}}:
      Some{value}
    case _:
      None{}

def string_entry.found(found: Maybe<&2, Core.Declaration>) -> Maybe<&2, String>:
  match found:
    case Some{Core.Definition{Core.Header{_, _, 0, _}, 0, False{}, Nil{}, _, Some{body}}}:
      string_entry.term(body)
    case _:
      None{}

def string_entry(+decls: List<&2, Core.Declaration>, name: String) -> Maybe<&2, String>:
  string_entry.found(Core.find(decls, name))

def is_contract(found: Maybe<&2, String>) -> Bool:
  match found:
    case None{}:
      True{}
    case Some{_}:
      False{}

# The first entry that is a contract function. Its result type names the
# Evm module.
def contract.first(names: List<&2, String>, +decls: List<&2, Core.Declaration>) -> Result<&2, &2, String, String>:
  match names:
    case Nil{}:
      Fail{"Name at least one contract function"}
    case +name <> rest:
      Bool.pick(Result<&2, &2, String, String>, is_contract(string_entry(decls, name)), Done{name}, contract.first(rest, decls))
