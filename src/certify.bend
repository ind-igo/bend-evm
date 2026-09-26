import Base
import ./ir.bend as IR
import ./read.bend as Read
import ./tool.bend as Tool

# Prints Bend source that restates each entry as IR and proves the two equal.
# Usage: certify.bend <contract.bend> <function>... > <contract dir>/CERT.bend

def nat(n: Nat) -> String:
  Nat.show(n) ++ "n"

def show.expr(e: IR.Expr) -> String:
  match e:
    case IR.Lit{value}:
      "IR.Lit{" ++ nat(value) ++ "}"
    case IR.Var{level}:
      "IR.Var{" ++ nat(level) ++ "}"

def show.two(name: String, left: IR.Expr, right: IR.Expr) -> String:
  l r = show.expr(left) show.expr(right)
  name ++ "{" ++ l ++ ", " ++ r ++ "}"

def show.cond(c: IR.Cond) -> String:
  match c:
    case IR.Eq{left, right}:
      show.two("IR.Eq", left, right)
    case IR.Lt{left, right}:
      show.two("IR.Lt", left, right)
    case IR.Not{c}:
      "IR.Not{" ++ show.cond(c) ++ "}"

def show.loc(l: IR.Loc) -> String:
  match l:
    case IR.Plain{slot}:
      "IR.Plain{" ++ show.expr(slot) ++ "}"
    case IR.Mapped{base, key}:
      "IR.Mapped{" ++ show.loc(base) ++ ", " ++ show.expr(key) ++ "}"

def show.list(exprs: List<&2, IR.Expr>) -> List<&2, String>:
  match exprs:
    case Nil{}:
      Nil{}
    case e <> rest:
      show.expr(e) <> show.list(rest)

def show.word(w: IR.Word) -> String:
  match w:
    case IR.SLoad{l}:
      "IR.SLoad{" ++ show.loc(l) ++ "}"
    case IR.Caller{}:
      "IR.Caller{}"
    case IR.Add{left, right}:
      show.two("IR.Add", left, right)
    case IR.Sub{left, right}:
      show.two("IR.Sub", left, right)
    case IR.Select{c, yes, no}:
      "IR.Select{" ++ show.cond(c) ++ ", " ++ show.expr(yes) ++ ", " ++ show.expr(no) ++ "}"
    case IR.Max{}:
      "IR.Max{}"
    case IR.Timestamp{}:
      "IR.Timestamp{}"
    case IR.ChainId{}:
      "IR.ChainId{}"
    case IR.Self{}:
      "IR.Self{}"
    case IR.Keccak{words}:
      "IR.Keccak{[" ++ String.join(show.list(words), ", ") ++ "]}"
    case IR.Typed{domain, message}:
      show.two("IR.Typed", domain, message)
    case IR.Id{text}:
      "IR.Id{\"" ++ text ++ "\"}"
    case IR.Recover{digest, v, r, s}:
      "IR.Recover{" ++ String.join(show.list([digest, v, r, s]), ", ") ++ "}"
    case IR.View{target, signature, args}:
      "IR.View{" ++ show.expr(target) ++ ", \"" ++ signature ++ "\", [" ++ String.join(show.list(args), ", ") ++ "]}"

# The reader only accepts signature characters, so the quotes stay closed.
def show.effect(e: IR.Effect) -> String:
  match e:
    case IR.Log{event, topics, data}:
      "IR.Log{\"" ++ event ++ "\", [" ++ String.join(show.list(topics), ", ") ++ "], [" ++ String.join(show.list(data), ", ") ++ "]}"
    case IR.SStore{l, value}:
      "IR.SStore{" ++ show.loc(l) ++ ", " ++ show.expr(value) ++ "}"
    case IR.Require{c}:
      "IR.Require{" ++ show.cond(c) ++ "}"
    case IR.Ensure{c, error, args}:
      "IR.Ensure{" ++ show.cond(c) ++ ", \"" ++ error ++ "\", [" ++ String.join(show.list(args), ", ") ++ "]}"

def show.cmd(c: IR.Cmd) -> String:
  match c:
    case IR.Bind{w, level, body}:
      a b = show.word(w) show.cmd(body)
      "IR.Bind{" ++ a ++ ", " ++ nat(level) ++ ",\n    " ++ b ++ "}"
    case IR.Then{e, body}:
      a b = show.effect(e) show.cmd(body)
      "IR.Then{" ++ a ++ ",\n    " ++ b ++ "}"
    case IR.Return{value}:
      "IR.Return{" ++ show.expr(value) ++ "}"
    case IR.Tail{w}:
      "IR.Tail{" ++ show.word(w) ++ "}"
    case IR.Finish{e}:
      "IR.Finish{" ++ show.effect(e) ++ "}"
    case IR.Stop{}:
      "IR.Stop{}"
    case IR.If{c, yes, no}:
      a b = show.cmd(yes) show.cmd(no)
      "IR.If{" ++ show.cond(c) ++ ",\n    " ++ a ++ ",\n    " ++ b ++ "}"

def param(+level: Nat) -> String:
  "p" ++ Nat.show(level)

def fors(levels: List<&2, Nat>) -> String:
  match levels:
    case Nil{}:
      ""
    case +level <> rest:
      "  for +" ++ param(level) ++ ": Nat\n" ++ fors(rest)

def bindings(levels: List<&2, Nat>) -> List<&2, String>:
  match levels:
    case Nil{}:
      Nil{}
    case +level <> rest:
      ("IR.Binding{" ++ nat(level) ++ ", " ++ param(level) ++ "}") <> bindings(rest)

def names(levels: List<&2, Nat>) -> List<&2, String>:
  match levels:
    case Nil{}:
      Nil{}
    case +level <> rest:
      param(level) <> names(rest)

def output(out: IR.Output) -> String & String:
  match out:
    case IR.Returns{}:
      ("IR.Returns{}", "Nat")
    case IR.Stops{}:
      ("IR.Stops{}", "Unit")

def claim.text(+name: String, +levels: List<&2, Nat>, body: IR.Cmd, kind: String & String) -> String:
  match kind:
    case Tuple{out, typ}:
      +args = String.join(names(levels), ", ")
      "def ir." ++ name ++ "() -> IR.Cmd:\n  " ++ show.cmd(body) ++ "\n\n"
        ++ "law " ++ name ++ ":\n" ++ fors(levels)
        ++ "  {IR.call(ir." ++ name ++ "(), " ++ out ++ ", [" ++ String.join(bindings(levels), ", ") ++ "])"
        ++ " == Program." ++ name ++ "(" ++ args ++ ") : Evm.Contract(" ++ typ ++ ")}\n\n"
        ++ "def " ++ name ++ "(" ++ args ++ "):\n  {==}\n\n"

# A constant string entry is not a contract, so it has no claim.
def claim(f: Read.Function) -> String:
  match f:
    case Read.Constant{_, _}:
      ""
    case Read.Contract{+name, _, _, Read.Entry{+levels, +body}}:
      claim.text(name, levels, body, output(Read.output(body)))

def claims(fs: List<&2, Read.Function>) -> String:
  match fs:
    case Nil{}:
      ""
    case f <> rest:
      claim(f) ++ claims(rest)

# evm is the Evm module's name prefix, such as "../Evm."; ir.bend sits beside it.
def header(+evm: String, file: String) -> String:
  "# Generated by src/certify.bend. Do not edit; check it with Bend.\n"
    ++ "import Base\n"
    ++ "import " ++ Tool.evm.path(evm) ++ ".bend as Evm\n"
    ++ "import " ++ Tool.otherwise("", Read.before("Evm.", evm)) ++ "ir.bend as IR\n"
    ++ "import ./" ++ Read.after_last('/', file) ++ " as Program\n\n"

def certificate(file: String, s: Tool.Setup) -> Result<&2, &2, String, String>:
  match s:
    case Tool.Setup{+evm, fs, _}:
      Done{header(evm, file) ++ claims(fs)}

def main() -> IO(Unit):
  Tool.main(~certificate, "Usage: certify.bend <contract.bend> <function>...")
