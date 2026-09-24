import Base

# Keccak-256 of one block (up to 135 bytes), enough for ABI selectors.
# A 64-bit lane is two U32 halves; the state is a list of 25 lanes, x + 5y.
type Lane is Data:
  Lane{hi: U32, lo: U32}

def xor(a: Lane, b: Lane) -> Lane:
  match a b:
    case Lane{ah, al} Lane{bh, bl}:
      Lane{U32.xor(ah, bh), U32.xor(al, bl)}

# (not a) and b
def and_not(a: Lane, b: Lane) -> Lane:
  match a b:
    case Lane{ah, al} Lane{bh, bl}:
      Lane{U32.and(U32.not(ah), bh), U32.and(U32.not(al), bl)}

def top(x: U32) -> U32:
  Bool.pick(U32, U32.is_lt(x, 2147483648), 0, 1)

def rot1(a: Lane) -> Lane:
  match a:
    case Lane{+hi, +lo}:
      Lane{U32.or(U32.shl(hi), top(lo)), U32.or(U32.shl(lo), top(hi))}

# Rotate left by n bits.
def rot(n: Nat, a: Lane) -> Lane:
  match n:
    case 0n:
      a
    case 1n+p:
      rot(p, rot1(a))

def at(xs: List<&2, Lane>, n: Nat) -> Lane:
  match xs n:
    case Nil{} _:
      Lane{0, 0}
    case x <> _ 0n:
      x
    case _ <> rest 1n+p:
      at(rest, p)

def put(xs: List<&2, Lane>, n: Nat, v: Lane) -> List<&2, Lane>:
  match xs n:
    case Nil{} _:
      Nil{}
    case _ <> rest 0n:
      v <> rest
    case x <> rest 1n+p:
      x <> put(rest, p, v)

def mod5(n: Nat) -> Nat:
  Nat.mod(n, 5n)

def column(+st: List<&2, Lane>, +x: Nat) -> Lane:
  xor(at(st, x), xor(at(st, Nat.add(x, 5n)), xor(at(st, Nat.add(x, 10n)),
    xor(at(st, Nat.add(x, 15n)), at(st, Nat.add(x, 20n))))))

def theta.d(+st: List<&2, Lane>, +x: Nat) -> Lane:
  xor(column(st, mod5(Nat.add(x, 4n))), rot(1n, column(st, mod5(Nat.add(x, 1n)))))

def theta.go(lanes: List<&2, Lane>, +i: Nat, +ds: List<&2, Lane>) -> List<&2, Lane>:
  match lanes:
    case Nil{}:
      Nil{}
    case lane <> rest:
      xor(lane, at(ds, mod5(i))) <> theta.go(rest, Nat.add(i, 1n), ds)

def theta(+st: List<&2, Lane>) -> List<&2, Lane>:
  theta.go(st, 0n, [theta.d(st, 0n), theta.d(st, 1n), theta.d(st, 2n), theta.d(st, 3n), theta.d(st, 4n)])

# Rho and pi together: walk the lanes, rotating each into its next position.
type Step is Data:
  Step{lane: Nat, shift: Nat}

def steps() -> List<&2, Step>:
  [Step{10n, 1n}, Step{7n, 3n}, Step{11n, 6n}, Step{17n, 10n}, Step{18n, 15n}, Step{3n, 21n},
    Step{5n, 28n}, Step{16n, 36n}, Step{8n, 45n}, Step{21n, 55n}, Step{24n, 2n}, Step{4n, 14n},
    Step{15n, 27n}, Step{23n, 41n}, Step{19n, 56n}, Step{13n, 8n}, Step{12n, 25n}, Step{2n, 43n},
    Step{20n, 62n}, Step{14n, 18n}, Step{22n, 39n}, Step{9n, 61n}, Step{6n, 20n}, Step{1n, 44n}]

def rho_pi.go(path: List<&2, Step>, +st: List<&2, Lane>, t: Lane) -> List<&2, Lane>:
  match path:
    case Nil{}:
      st
    case Step{+j, r} <> rest:
      rho_pi.go(rest, put(st, j, rot(r, t)), at(st, j))

def rho_pi(+st: List<&2, Lane>) -> List<&2, Lane>:
  rho_pi.go(steps(), st, at(st, 1n))

def chi.go(lanes: List<&2, Lane>, +i: Nat, +st: List<&2, Lane>) -> List<&2, Lane>:
  match lanes:
    case Nil{}:
      Nil{}
    case lane <> rest:
      +x = mod5(i)
      +row = Nat.sub(i, x)
      next = and_not(at(st, Nat.add(row, mod5(Nat.add(x, 1n)))), at(st, Nat.add(row, mod5(Nat.add(x, 2n)))))
      xor(lane, next) <> chi.go(rest, Nat.add(i, 1n), st)

def chi(+st: List<&2, Lane>) -> List<&2, Lane>:
  chi.go(st, 0n, st)

def iota(st: List<&2, Lane>, rc: Lane) -> List<&2, Lane>:
  match st:
    case Nil{}:
      Nil{}
    case lane <> rest:
      xor(lane, rc) <> rest

def constants() -> List<&2, Lane>:
  [Lane{0, 1}, Lane{0, 32898}, Lane{2147483648, 32906},
    Lane{2147483648, 2147516416}, Lane{0, 32907}, Lane{0, 2147483649},
    Lane{2147483648, 2147516545}, Lane{2147483648, 32777}, Lane{0, 138},
    Lane{0, 136}, Lane{0, 2147516425}, Lane{0, 2147483658},
    Lane{0, 2147516555}, Lane{2147483648, 139}, Lane{2147483648, 32905},
    Lane{2147483648, 32771}, Lane{2147483648, 32770}, Lane{2147483648, 128},
    Lane{0, 32778}, Lane{2147483648, 2147483658}, Lane{2147483648, 2147516545},
    Lane{2147483648, 32896}, Lane{0, 2147483649}, Lane{2147483648, 2147516424}]

def rounds(constants: List<&2, Lane>, st: List<&2, Lane>) -> List<&2, Lane>:
  match constants:
    case Nil{}:
      st
    case rc <> rest:
      rounds(rest, iota(chi(rho_pi(theta(st))), rc))

# The block: the bytes, then 0x01, then zeros, with 0x80 xored into byte 135.
def pad(n: Nat, msg: List<&2, U32>, +marked: Bool) -> List<&2, U32>:
  match n msg:
    case 0n _:
      Nil{}
    case 1n+(+p) Nil{}:
      +mark = Bool.pick(U32, marked, 0, 1)
      +last = Bool.pick(U32, Nat.is_eq(p, 0n), 128, 0)
      U32.xor(mark, last) <> pad(p, Nil{}, True{})
    case 1n+(+p) b <> rest:
      U32.xor(b, Bool.pick(U32, Nat.is_eq(p, 0n), 128, 0)) <> pad(p, rest, marked)

def word(b0: U32, b1: U32, b2: U32, b3: U32) -> U32:
  U32.add(b0, U32.mul(256, U32.add(b1, U32.mul(256, U32.add(b2, U32.mul(256, b3))))))

# Little-endian lanes: bytes 0-3 are the low half.
def lanes(bytes: List<&2, U32>) -> List<&2, Lane>:
  match bytes:
    case b0 <> b1 <> b2 <> b3 <> b4 <> b5 <> b6 <> b7 <> rest:
      Lane{word(b4, b5, b6, b7), word(b0, b1, b2, b3)} <> lanes(rest)
    case _:
      Nil{}

def codes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, rest}:
      Char.to_u32(c) <> codes(rest)

def zeros(n: Nat) -> List<&2, Lane>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Lane{0, 0} <> zeros(p)

def hash(s: String) -> List<&2, Lane>:
  block = lanes(pad(136n, codes(s), False{}))
  rounds(constants(), List.append(&2, Lane, block, zeros(8n)))

def byte(x: U32, shift: Nat) -> U32:
  U32.and(U32.shrn(x, shift), 255)

# The first four bytes of the hash, big-endian.
def selector.lane(a: Lane) -> U32:
  match a:
    case Lane{_, +lo}:
      word(byte(lo, 24n), byte(lo, 16n), byte(lo, 8n), byte(lo, 0n))

# One block holds up to 135 bytes; longer input would hash wrongly.
def fits(s: String) -> Bool:
  Nat.is_lt(String.length(s), 136n)

def selector(signature: String) -> U32:
  selector.lane(at(hash(signature), 0n))

def hex.digit(+d: U32) -> Char:
  Bool.pick(Char, U32.is_lt(d, 10), Char.from_u32(U32.add(d, 48)), Char.from_u32(U32.add(d, 87)))

def hex.go(n: Nat, x: U32) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+p:
      +v = x
      SCon{hex.digit(U32.shrn(v, 28n)), hex.go(p, U32.shln(v, 4n))}

def hex.byte(+b: U32) -> String:
  SCon{hex.digit(U32.shrn(b, 4n)), SCon{hex.digit(U32.and(b, 15)), SNil{}}}

# A lane's bytes in memory order: the low half first, each half little-endian.
def hex.half(+x: U32) -> String:
  hex.byte(byte(x, 0n)) ++ hex.byte(byte(x, 8n)) ++ hex.byte(byte(x, 16n)) ++ hex.byte(byte(x, 24n))

def hex.lane(a: Lane) -> String:
  match a:
    case Lane{hi, lo}:
      hex.half(lo) ++ hex.half(hi)

def digest.go(n: Nat, lanes: List<&2, Lane>) -> String:
  match n lanes:
    case 1n+p a <> rest:
      hex.lane(a) ++ digest.go(p, rest)
    case _ _:
      ""

# The full 32-byte hash as a 0x-prefixed Yul literal.
def digest(s: String) -> String:
  "0x" ++ digest.go(4n, hash(s))

# Eight lowercase hex digits with a 0x prefix.
def hex(x: U32) -> String:
  "0x" ++ hex.go(8n, x)
