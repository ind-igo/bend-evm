import Base

# The contract model. Words are Nat below the state's limit (2^256 on the EVM).
# Storage is an association list: the newest slot wins, missing slots are zero.
# A key is a plain slot or an entry of the mapping at base, which may itself
# be an entry. On the EVM an entry lives at keccak256(key . base), as in
# Solidity; the model assumes no collisions.
type Key is Data:
  Plain{slot: Nat}
  Mapped{base: Key, key: Nat}

def same(a: Key, b: Key) -> Bool:
  match a b:
    case Plain{x} Plain{y}:
      Nat.is_eq(x, y)
    case Mapped{x, k} Mapped{y, j}:
      Bool.and(same(x, y), Nat.is_eq(k, j))
    case Plain{_} Mapped{_, _}:
      False{}
    case Mapped{_, _} Plain{_}:
      False{}

type Slot is Data:
  Slot{key: Key, value: Nat}

# An address is a word below 2^160. The ABI dispatcher reverts on a larger
# `address` argument, so a contract may use Address for parameters that are one.
def Address() -> Data:
  Nat

# A uint8 word, such as an ERC-20's decimals. The dispatcher reverts on a
# larger argument.
def Uint8() -> Data:
  Nat

# A bytes32 word, such as a signature's r and s. Every word is one.
def Bytes32() -> Data:
  Nat

# A bool word: 1 is true and 0 is false. The dispatcher reverts on a larger
# argument.
def Boolean() -> Data:
  Nat

# An indexed event field: its word is a topic, not data. See emit.
def Indexed(A: Data) -> Data:
  A

# A log entry: an event's signature, such as "Transfer(address,address,uint256)",
# the indexed words after topic 0, and the data words. Topic 0 is the
# signature's Keccak-256, which the printer computes.
type Log is Data:
  Log{signature: String, topics: List<&2, Nat>, data: List<&2, Nat>}

# The result type of an event def, which is its log. The reader compiles
# Evm.emit only for a def written with this result type:
#   def Transfer(from: Evm.Indexed(Evm.Address), to: Evm.Indexed(Evm.Address), amount: Nat) -> Evm.Event:
#     Evm.Log{"Transfer(address,address,uint256)", [from, to], [amount]}
def Event() -> Data:
  Log

# A custom error: its signature, such as "Unauthorized(address)", and its
# argument words. The revert data is the signature's 4-byte selector, then
# the words, which the printer encodes. An error def gives it, and
# Evm.ensure reverts with it:
#   def Unauthorized(account: Evm.Address) -> Evm.Error:
#     Evm.Error{"Unauthorized(address)", [account]}
type Error is Data:
  Error{signature: String, args: List<&2, Nat>}

# What keccak256 hashes: words of 32 bytes; an EIP-712 digest, which hashes
# 0x1901 . domain . message; or an ASCII text, such as a type string.
type Preimage is Data:
  Words{words: List<&2, Nat>}
  Typed{domain: Nat, message: Nat}
  Text{text: String}

type Hashed is Data:
  Hashed{preimage: Preimage, hash: Nat}

type Signed is Data:
  Signed{digest: Nat, v: Nat, r: Nat, s: Nat, signer: Nat}

# The chain around a call: the block time, the chain id, the contract's own
# address, and tables that stand for keccak256 and ecrecover. A law holds for
# every table, so no law depends on how either function works; the printer
# uses the real ones. A missing entry reads as zero, as ecrecover gives zero
# for a bad signature.
type World is Data:
  World{time: Nat, chain: Nat, self: Nat, hashes: List<&2, Hashed>, signers: List<&2, Signed>}

# A call's state. Logs are newest first. The word limit is state, not a
# constant: a symbolic limit keeps proofs from expanding 2^256 as a unary
# Nat, and laws proved for every limit hold on the EVM.
type State is Data:
  State{storage: List<&2, Slot>, caller: Nat, limit: Nat, logs: List<&2, Log>, world: World}

def storage.of(s: State) -> List<&2, Slot>:
  match s:
    case State{storage, _, _, _, _}:
      storage

def caller.of(s: State) -> Nat:
  match s:
    case State{_, caller, _, _, _}:
      caller

def limit.of(s: State) -> Nat:
  match s:
    case State{_, _, limit, _, _}:
      limit

def world.of(s: State) -> World:
  match s:
    case State{_, _, _, _, world}:
      world

def time.of(w: World) -> Nat:
  match w:
    case World{time, _, _, _, _}:
      time

def chain.of(w: World) -> Nat:
  match w:
    case World{_, chain, _, _, _}:
      chain

def self.of(w: World) -> Nat:
  match w:
    case World{_, _, self, _, _}:
      self

def same.words(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case x <> xs y <> ys:
      Bool.and(Nat.is_eq(x, y), same.words(xs, ys))
    case _ _:
      False{}

def same.preimage(a: Preimage, b: Preimage) -> Bool:
  match a b:
    case Words{x} Words{y}:
      same.words(x, y)
    case Typed{d, m} Typed{e, n}:
      Bool.and(Nat.is_eq(d, e), Nat.is_eq(m, n))
    case Text{x} Text{y}:
      String.eq(x, y)
    case _ _:
      False{}

def hash.of(hashes: List<&2, Hashed>, +p: Preimage) -> Nat:
  match hashes:
    case Nil{}:
      0n
    case Hashed{q, h} <> rest:
      Bool.pick(Nat, same.preimage(q, p), h, hash.of(rest, p))

def signer.of(signers: List<&2, Signed>, +digest: Nat, +v: Nat, +r: Nat, +s: Nat) -> Nat:
  match signers:
    case Nil{}:
      0n
    case Signed{d, x, y, z, who} <> rest:
      Bool.pick(Nat, Bool.and(Bool.and(Nat.is_eq(d, digest), Nat.is_eq(x, v)), Bool.and(Nat.is_eq(y, r), Nat.is_eq(z, s))),
        who, signer.of(rest, digest, v, r, s))

def hashes.of(w: World) -> List<&2, Hashed>:
  match w:
    case World{_, _, _, hashes, _}:
      hashes

def signers.of(w: World) -> List<&2, Signed>:
  match w:
    case World{_, _, _, _, signers}:
      signers

# A revert discards every state change, so it carries no state. Revert has
# no revert data; Raise has a custom error's.
type Outcome<-A: Data> is Data:
  Ok{value: A, state: State}
  Revert{}
  Raise{error: Error}

# A contract passes its result and state to a continuation. A check is then
# a Bool.pick at the top of the contract's normal form, not a match stuck
# inside a bind, so a law can state every outcome and {==} proves it.
def Contract(-A: Data) -> Type:
  @-R: Data -> @k: (A -> State -> Outcome<R>) -> State -> Outcome<R>

def Contract.pure(-A: Data, x: A) -> Contract(A):
  R => k => s => k(x, s)

def Contract.bind(-A: Data, -B: Data, m: Contract(A), f: A -> Contract(B)) -> Contract(B):
  R => k => m(R, x => f(x, R, k))

# Runs a contract from a state to its outcome.
def run(-A: Data, m: Contract(A), s: State) -> Outcome<A>:
  m(A, x => t => Ok{x, t}, s)

def lookup(storage: List<&2, Slot>, +key: Key) -> Nat:
  match storage:
    case Nil{}:
      0n
    case Slot{k, v} <> rest:
      Bool.pick(Nat, same(k, key), v, lookup(rest, key))

# read, write and log are the model's primitives. Contracts use the DSL calls
# built on them (sload, store2, emit, ...), which the reader knows.
def read(+key: Key) -> Contract(Nat):
  R => k => +s => k(lookup(storage.of(s), key), s)

def sload(slot: Nat) -> Contract(Nat):
  read(Plain{slot})

# The value at key in the mapping at slot.
def load(slot: Nat, key: Nat) -> Contract(Nat):
  read(Mapped{Plain{slot}, key})

# The value at inner in the mapping at outer in the mapping at slot.
def load2(slot: Nat, outer: Nat, inner: Nat) -> Contract(Nat):
  read(Mapped{Mapped{Plain{slot}, outer}, inner})

def write.go(key: Key, value: Nat, s: State) -> State:
  match s:
    case State{storage, caller, limit, logs, world}:
      State{Slot{key, value} <> storage, caller, limit, logs, world}

def write(key: Key, value: Nat) -> Contract(Unit):
  R => k => s => k(Unit{}, write.go(key, value, s))

def sstore(slot: Nat, value: Nat) -> Contract(Unit):
  write(Plain{slot}, value)

def store(slot: Nat, key: Nat, value: Nat) -> Contract(Unit):
  write(Mapped{Plain{slot}, key}, value)

def store2(slot: Nat, outer: Nat, inner: Nat, value: Nat) -> Contract(Unit):
  write(Mapped{Mapped{Plain{slot}, outer}, inner}, value)

def caller() -> Contract(Nat):
  R => k => +s => k(caller.of(s), s)

def log.go(event: String, topics: List<&2, Nat>, data: List<&2, Nat>, s: State) -> State:
  match s:
    case State{storage, caller, limit, logs, world}:
      State{storage, caller, limit, Log{event, topics, data} <> logs, world}

def log(event: String, topics: List<&2, Nat>, data: List<&2, Nat>) -> Contract(Unit):
  R => k => s => k(Unit{}, log.go(event, topics, data, s))

# Logs an event, as in Evm.emit(ERC20.Transfer(from, to, amount)), where an
# event is a def from its fields to Evm.Event. The reader takes the signature
# and the topics from the def's parameter types, and the certificate checks
# that its body gives the same log.
def emit(l: Event) -> Contract(Unit):
  match l:
    case Log{event, topics, data}:
      log(event, topics, data)

def require(ok: Bool) -> Contract(Unit):
  R => k => s => Bool.pick(Outcome<R>, ok, k(Unit{}, s), Revert{})

# Reverts with a custom error unless ok holds, as Solidity's
# require(ok, Unauthorized(who)) does. The reader takes the signature from
# the error def's name and parameter types, and the certificate checks that
# its body gives the same error.
def ensure(ok: Bool, e: Error) -> Contract(Unit):
  R => k => s => Bool.pick(Outcome<R>, ok, k(Unit{}, s), Raise{e})

# a when ok holds, b otherwise. It chooses a word, not a contract, so the
# continuation is used once and laws stay closed.
def select(ok: Bool, a: Nat, b: Nat) -> Contract(Nat):
  R => k => s => k(Bool.pick(Nat, ok, a, b), s)

# Runs a when ok holds and b otherwise, to the end of the call. It picks a
# whole contract, so the continuation goes to one arm and is not copied. Code
# that both arms run after the choice goes in each arm, as a call to a def.
def branch(-A: Data, ok: Bool, a: Contract(A), b: Contract(A)) -> Contract(A):
  Bool.pick(Contract(A), ok, a, b)

# The outcome of a branch is the outcome of its arm. When ok is not known, a
# run stops at the branch, so a law about it uses this fact.
def branch.run(-A: Data, ok: Bool, -a: Contract(A), -b: Contract(A), +s: State) ->
  {run(A, branch(A, ok, a, b), s) == Bool.pick(Outcome<A>, ok, run(A, a, s), run(A, b, s)) : Outcome<A>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# The largest word, 2^256 - 1 on the EVM.
def max() -> Contract(Nat):
  R => k => +s => k(Nat.sub(limit.of(s), 1n), s)

# The block's timestamp, the chain id and the contract's own address.
def timestamp() -> Contract(Nat):
  R => k => +s => k(time.of(world.of(s)), s)

def chainid() -> Contract(Nat):
  R => k => +s => k(chain.of(world.of(s)), s)

def self() -> Contract(Nat):
  R => k => +s => k(self.of(world.of(s)), s)

# keccak256 of words, of an EIP-712 digest, and of an ASCII text.
def keccak(words: List<&2, Nat>) -> Contract(Nat):
  R => k => +s => k(hash.of(hashes.of(world.of(s)), Words{words}), s)

def typed(domain: Nat, message: Nat) -> Contract(Nat):
  R => k => +s => k(hash.of(hashes.of(world.of(s)), Typed{domain, message}), s)

def id(text: String) -> Contract(Nat):
  R => k => +s => k(hash.of(hashes.of(world.of(s)), Text{text}), s)

# The address that signed digest, or zero, like ecrecover.
def recover(digest: Nat, v: Nat, r: Nat, sig: Nat) -> Contract(Nat):
  R => k => +s => k(signer.of(signers.of(world.of(s)), digest, v, r, sig), s)

# Checked addition: reverts on overflow, like Solidity 0.8.
def add(+a: Nat, +b: Nat) -> Contract(Nat):
  R => k => +s => Bool.pick(Outcome<R>, Nat.is_lt(Nat.add(a, b), limit.of(s)), k(Nat.add(a, b), s), Revert{})

# Checked subtraction: reverts when a < b, like Solidity 0.8.
def sub(+a: Nat, +b: Nat) -> Contract(Nat):
  R => k => s => Bool.pick(Outcome<R>, Nat.is_lt(a, b), Revert{}, k(Nat.sub(a, b), s))
