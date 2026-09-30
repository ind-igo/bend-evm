import Base

# The contract model. Words are Nat below the state's limit (2^256 on the EVM).
# Storage is an association list: the newest slot wins, missing slots are zero.
# A key is a plain slot or an entry of the mapping at base, which may itself
# be an entry. On the EVM an entry lives at keccak256(key . base), as in
# Solidity; the model assumes no collisions. A transient slot is in the
# EVM's transient storage (EIP-1153), which is apart from storage and which
# the EVM clears at the end of each transaction.
type Key is Data:
  Plain{slot: Nat}
  Mapped{base: Key, key: Nat}
  Transient{slot: Nat}

def same(a: Key, b: Key) -> Bool:
  match a b:
    case Plain{x} Plain{y}:
      Nat.is_eq(x, y)
    case Mapped{x, k} Mapped{y, j}:
      Bool.and(same(x, y), Nat.is_eq(k, j))
    case Transient{x} Transient{y}:
      Nat.is_eq(x, y)
    case _ _:
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

# An int256 word, in two's complement: a word from 2^255 up is negative.
# Every word is one. Evm.slt, Evm.sgt, Evm.sdiv, Evm.smod and Evm.sar read
# it as signed.
def Int() -> Data:
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

# A log entry: an event's name, such as "Transfer", the indexed words after
# topic 0, and the data words. Topic 0 is the Keccak-256 of the signature,
# such as "Transfer(address,address,uint256)", which the reader builds from
# the event def's name and parameter types.
#
# Logs, errors and calls hold a name, not a signature: Bend cannot see a
# def's name or tell its parameter types apart (Evm.Address is Nat), so the
# body gives the name and the reader gives the types. The certificate checks
# that the name is the def's own. Two defs of one kind with one name must
# have one signature, as the model cannot tell them apart.
#
# An event def returns its log. The reader compiles Evm.emit only for a def
# written with this result type:
#   def Transfer(from: Evm.Indexed(Evm.Address), to: Evm.Indexed(Evm.Address), amount: Nat) -> Evm.Log:
#     Evm.Log{"Transfer", [from, to], [amount]}
type Log is Data:
  Log{name: String, topics: List<&2, Nat>, data: List<&2, Nat>}

# A custom error: its name and its argument words. The revert data is the
# 4-byte selector of its signature, such as "Unauthorized(address)", then
# the words, which the printer encodes. An error def gives it, and
# Evm.ensure reverts with it:
#   def Unauthorized(account: Evm.Address) -> Evm.Error:
#     Evm.Error{"Unauthorized", [account]}
type Error is Data:
  Error{name: String, args: List<&2, Nat>}

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

# A call to another contract: its address, the function's name and the
# argument words. The calldata is the 4-byte selector of its signature, such
# as "balanceOf(address)", then the words. An interface def gives it, and
# Evm.view or Evm.call makes it:
#   def balanceOf(token: Evm.Address, who: Evm.Address) -> Evm.Call:
#     Evm.Call{token, "balanceOf", [who]}
#
# Pay is a call that sends amount wei with no data, which Evm.pay makes.
type Call is Data:
  Call{target: Nat, name: String, args: List<&2, Nat>}
  Pay{target: Nat, amount: Nat}

type Answer is Data:
  Answer{call: Call, value: Nat}

# A value that a contract reads from its environment: the transaction, the
# block or an account. Values that cannot change during a transaction come
# from a table; the others (fixed is False) come from a list of readings,
# one for each read, so no law depends on two reads being the same.
type Env is Data:
  Timestamp{}
  ChainId{}
  Origin{}
  GasPrice{}
  Coinbase{}
  Number{}
  PrevRandao{}
  GasLimit{}
  BaseFee{}
  BlobBaseFee{}
  BlockHash{}
  BlobHash{}
  CodeSize{}
  Gas{}
  Balance{}
  SelfBalance{}
  ExtCodeSize{}
  ExtCodeHash{}
  CallValue{}

# An operation's or an environment value's constructor, Yul name, name in a
# contract, and number of words. Solidity checks add, sub, mul, div, mod and
# **, so a contract names their word operations Evm.unchecked.add and so on.
type Info is Data:
  Info{con: String, yul: String, name: String, arity: Nat}

# An environment value's names and number of words, its opcode, and whether
# it is fixed in a transaction.
type Sensor is Data:
  Sensor{info: Info, code: Nat, fixed: Bool}

def sensor(e: Env) -> Sensor:
  match e:
    case Timestamp{}:
      Sensor{Info{"Timestamp", "timestamp", "timestamp", 0n}, 66n, True{}}
    case ChainId{}:
      Sensor{Info{"ChainId", "chainid", "chainid", 0n}, 70n, True{}}
    case Origin{}:
      Sensor{Info{"Origin", "origin", "origin", 0n}, 50n, True{}}
    case GasPrice{}:
      Sensor{Info{"GasPrice", "gasprice", "gasprice", 0n}, 58n, True{}}
    case Coinbase{}:
      Sensor{Info{"Coinbase", "coinbase", "coinbase", 0n}, 65n, True{}}
    case Number{}:
      Sensor{Info{"Number", "number", "number", 0n}, 67n, True{}}
    case PrevRandao{}:
      Sensor{Info{"PrevRandao", "prevrandao", "prevrandao", 0n}, 68n, True{}}
    case GasLimit{}:
      Sensor{Info{"GasLimit", "gaslimit", "gaslimit", 0n}, 69n, True{}}
    case BaseFee{}:
      Sensor{Info{"BaseFee", "basefee", "basefee", 0n}, 72n, True{}}
    case BlobBaseFee{}:
      Sensor{Info{"BlobBaseFee", "blobbasefee", "blobbasefee", 0n}, 74n, True{}}
    case BlockHash{}:
      Sensor{Info{"BlockHash", "blockhash", "blockhash", 1n}, 64n, True{}}
    case BlobHash{}:
      Sensor{Info{"BlobHash", "blobhash", "blobhash", 1n}, 73n, True{}}
    case CodeSize{}:
      Sensor{Info{"CodeSize", "codesize", "codesize", 0n}, 56n, True{}}
    case Gas{}:
      Sensor{Info{"Gas", "gas", "gas", 0n}, 90n, False{}}
    case Balance{}:
      Sensor{Info{"Balance", "balance", "balance", 1n}, 49n, False{}}
    case SelfBalance{}:
      Sensor{Info{"SelfBalance", "selfbalance", "selfbalance", 0n}, 71n, False{}}
    case ExtCodeSize{}:
      Sensor{Info{"ExtCodeSize", "extcodesize", "extcodesize", 1n}, 59n, False{}}
    case ExtCodeHash{}:
      Sensor{Info{"ExtCodeHash", "extcodehash", "extcodehash", 1n}, 63n, False{}}
    case CallValue{}:
      Sensor{Info{"CallValue", "callvalue", "callvalue", 0n}, 52n, False{}}

def envs() -> List<&2, Env>:
  [Timestamp{}, ChainId{}, Origin{}, GasPrice{}, Coinbase{}, Number{}, PrevRandao{}, GasLimit{}, BaseFee{}, BlobBaseFee{},
  BlockHash{}, BlobHash{}, CodeSize{}, Gas{}, Balance{}, SelfBalance{}, ExtCodeSize{}, ExtCodeHash{}, CallValue{}]

def info.of(x: Sensor) -> Info:
  match x:
    case Sensor{i, _, _}:
      i

def code.of(x: Sensor) -> Nat:
  match x:
    case Sensor{_, c, _}:
      c

def fixed.of(x: Sensor) -> Bool:
  match x:
    case Sensor{_, _, f}:
      f

def code(e: Env) -> Nat:
  code.of(sensor(e))

def fixed(e: Env) -> Bool:
  fixed.of(sensor(e))

type Fact is Data:
  Fact{env: Env, args: List<&2, Nat>, value: Nat}

# The chain around a call: the table of fixed values, the readings, the
# contract's own address, tables that stand for keccak256 and ecrecover,
# and the answers of the view calls in the order the contract makes them. A
# law holds for every table and every list of readings and answers, so no
# law depends on how these functions or other contracts work; the printer
# uses the real ones. A missing entry reads as zero, as ecrecover gives zero
# for a bad signature.
type World is Data:
  World{facts: List<&2, Fact>, readings: List<&2, Nat>, self: Nat, hashes: List<&2, Hashed>, signers: List<&2, Signed>,
    answers: List<&2, Answer>}

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

def facts.of(w: World) -> List<&2, Fact>:
  match w:
    case World{facts, _, _, _, _, _}:
      facts

def readings.of(w: World) -> List<&2, Nat>:
  match w:
    case World{_, readings, _, _, _, _}:
      readings

def self.of(w: World) -> Nat:
  match w:
    case World{_, _, self, _, _, _}:
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

def same.call(a: Call, b: Call) -> Bool:
  match a b:
    case Call{t, f, x} Call{u, g, y}:
      Bool.and(Nat.is_eq(t, u), Bool.and(String.eq(f, g), same.words(x, y)))
    case Pay{t, x} Pay{u, y}:
      Bool.and(Nat.is_eq(t, u), Nat.is_eq(x, y))
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

def fact.of(facts: List<&2, Fact>, +e: Env, +args: List<&2, Nat>) -> Nat:
  match facts:
    case Nil{}:
      0n
    case Fact{f, a, v} <> rest:
      Bool.pick(Nat, Bool.and(Nat.is_eq(code(f), code(e)), same.words(a, args)), v, fact.of(rest, e, args))

# The block's timestamp and the chain id, which laws name.
def time.of(w: World) -> Nat:
  fact.of(facts.of(w), Timestamp{}, [])

def chain.of(w: World) -> Nat:
  fact.of(facts.of(w), ChainId{}, [])

def hashes.of(w: World) -> List<&2, Hashed>:
  match w:
    case World{_, _, _, hashes, _, _}:
      hashes

def signers.of(w: World) -> List<&2, Signed>:
  match w:
    case World{_, _, _, _, signers, _}:
      signers

# A revert discards every state change, so it carries no state. Revert has
# no revert data; Raise has a custom error's. Calling is a contract stopped
# at a call that may write: the call, the state, and the rest of the
# contract, which takes the returned word and the state after the call.
# calls.bend runs it with the answers and the callbacks. It holds a
# function, so an outcome is not Data.
type Outcome<-A: Data> is Type:
  Ok{value: A, state: State}
  Revert{}
  Raise{error: Error}
  Calling{call: Call, state: State, resume: Nat -> State -> Outcome<A>}

# A contract passes its result and state to a continuation. A check is then
# a Bool.pick at the top of the contract's normal form, not a match stuck
# inside a bind, so a law can state every outcome and {==} proves it.
def Contract(-A: Data) -> Type:
  @-R: Data -> @k: (A -> State -> Outcome<R>) -> State -> Outcome<R>

# The result type of a function that accepts ether, as Solidity's payable.
# Every other function reverts when it gets ether.
def Payable(-A: Data) -> Type:
  Contract(A)

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

# Transient storage, as Solidity's transient variables: tload(slot) and
# tstore(slot, value).
def tload(slot: Nat) -> Contract(Nat):
  read(Transient{slot})

def tstore(slot: Nat, value: Nat) -> Contract(Unit):
  write(Transient{slot}, value)

def caller() -> Contract(Nat):
  R => k => +s => k(caller.of(s), s)

def log.go(event: String, topics: List<&2, Nat>, data: List<&2, Nat>, s: State) -> State:
  match s:
    case State{storage, caller, limit, logs, world}:
      State{storage, caller, limit, Log{event, topics, data} <> logs, world}

def log(event: String, topics: List<&2, Nat>, data: List<&2, Nat>) -> Contract(Unit):
  R => k => s => k(Unit{}, log.go(event, topics, data, s))

# Logs an event, as in Evm.emit(ERC20.Transfer(from, to, amount)), where an
# event is a def from its fields to Evm.Log. The reader takes the signature
# and the topics from the def's parameter types, and the certificate checks
# that its body gives the same log.
def emit(l: Log) -> Contract(Unit):
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

# A value of the environment: a fixed one from the table, or the next
# reading, which the read uses up. No reading left reads as zero.
def first(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> _:
      x

def sense(+e: Env, +args: List<&2, Nat>, +s: State) -> Nat:
  Bool.pick(Nat, fixed(e), fact.of(facts.of(world.of(s)), e, args), first(readings.of(world.of(s))))

# The state after a read: a value that can change uses up a reading.
def used(s: State) -> State:
  match s:
    case State{storage, caller, limit, logs, World{facts, readings, self, hashes, signers, answers}}:
      State{storage, caller, limit, logs, World{facts, List.tail(&2, Nat, readings), self, hashes, signers, answers}}

def sensed(+e: Env, +s: State) -> State:
  Bool.pick(State, fixed(e), s, used(s))

def env(+e: Env, args: List<&2, Nat>) -> Contract(Nat):
  R => k => +s => k(sense(e, args, s), sensed(e, s))

# The contract's own address.
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

# The next answer, if it answers call c, goes to k with the rest of the
# answers. Otherwise the call failed or gave less than a word, and the
# contract reverts; a list of answers exists for each run on the EVM.
def answer(-R: Data, c: Call, k: Nat -> State -> Outcome<R>, s: State) -> Outcome<R>:
  match s:
    case State{storage, caller, limit, logs, World{facts, readings, self, hashes, signers, answers}}:
      match answers:
        case Nil{}:
          Revert{}
        case Answer{q, x} <> rest:
          Bool.pick(Outcome<R>, same.call(q, c),
            k(x, State{storage, caller, limit, logs, World{facts, readings, self, hashes, signers, rest}}), Revert{})

# Calls a function of another contract with staticcall and gives the first
# word it returns, as in IERC20(token).balanceOf(who). The reader takes the
# signature from the interface def's name and the parameter types after the
# first, which is the target, and the certificate checks that its body gives
# the same target, name and words. The called contract cannot change any state, but it can
# read this contract's state, so its answer is not a function of the call.
def view(c: Call) -> Contract(Nat):
  R => k => s => answer(R, c, k, s)

# Calls a function of another contract with call and gives the first word
# it returns, as in IERC20(token).transfer(to, amount). The called contract
# may call back into this one, so the contract stops here, and calls.bend
# runs the callbacks and gives the word. A law about it holds for every
# list of callbacks. The reader and the certificate treat the call as they
# treat a view's.
def call(c: Call) -> Contract(Nat):
  R => k => s => Calling{c, s, k}

# Sends amount wei to another account with call and no data, and reverts
# when the call fails, like solady's safeTransferETH. The receiver may call
# back into this contract, so the contract stops here, as at Evm.call.
def pay(to: Nat, amount: Nat) -> Contract(Unit):
  R => k => s => Calling{Pay{to, amount}, s, _ => t => k(Unit{}, t)}

# Checked addition: reverts on overflow, like Solidity 0.8.
def add(+a: Nat, +b: Nat) -> Contract(Nat):
  R => k => +s => Bool.pick(Outcome<R>, Nat.is_lt(Nat.add(a, b), limit.of(s)), k(Nat.add(a, b), s), Revert{})

# Checked subtraction: reverts when a < b, like Solidity 0.8.
def sub(+a: Nat, +b: Nat) -> Contract(Nat):
  R => k => s => Bool.pick(Outcome<R>, Nat.is_lt(a, b), Revert{}, k(Nat.sub(a, b), s))

# Checked multiplication: reverts on overflow, like Solidity 0.8.
def mul(+a: Nat, +b: Nat) -> Contract(Nat):
  R => k => +s => Bool.pick(Outcome<R>, Nat.is_lt(Nat.mul(a, b), limit.of(s)), k(Nat.mul(a, b), s), Revert{})

# Checked division and remainder: revert when b is zero, like Solidity 0.8.
def div(+a: Nat, +b: Nat) -> Contract(Nat):
  R => k => s => Bool.pick(Outcome<R>, Nat.is_eq(b, 0n), Revert{}, k(Nat.div(a, b), s))

def mod(+a: Nat, +b: Nat) -> Contract(Nat):
  R => k => s => Bool.pick(Outcome<R>, Nat.is_eq(b, 0n), Revert{}, k(Nat.mod(a, b), s))

# Word operations, as the EVM's opcodes compute them: modulo the limit, and
# never a revert. A word's width in bits and bytes comes from the limit, so
# they are the EVM's opcodes at the limit 2^256, and a model with a smaller
# limit has smaller words. The IR and the Yul model share these meanings.
type Op is Data:
  Add{}
  Sub{}
  Mul{}
  Div{}
  SDiv{}
  Mod{}
  SMod{}
  AddMod{}
  MulMod{}
  Exp{}
  SignExtend{}
  Lt{}
  Gt{}
  SLt{}
  SGt{}
  Eq{}
  IsZero{}
  And{}
  Or{}
  Xor{}
  Not{}
  Byte{}
  Shl{}
  Shr{}
  Sar{}

def bit(c: Bool) -> Nat:
  Bool.pick(Nat, c, 1n, 0n)

# Each recursive helper takes its fuel from its words and a flag that says
# it is done, so a proof about symbolic words does not unfold it, and a run
# stops as soon as it is done.

# The number of bits below n's highest bit: 256 at 2^256.
def width.go(fuel: Nat, small: Bool, +n: Nat) -> Nat:
  match fuel small:
    case 0n _:
      0n
    case 1n+_ True{}:
      0n
    case 1n+f False{}:
      +h = Nat.div(n, 2n)
      1n+width.go(f, Nat.is_lt(h, 2n), h)

def width(+l: Nat) -> Nat:
  width.go(l, Nat.is_lt(l, 2n), l)

# One bit of and, or or xor.
def gate(op: Op, +x: Nat, +y: Nat) -> Nat:
  match op:
    case And{}:
      Nat.mul(x, y)
    case Or{}:
      Nat.sub(Nat.add(x, y), Nat.mul(x, y))
    case _:
      Nat.mod(Nat.add(x, y), 2n)

def bitwise.go(fuel: Nat, zero: Bool, +op: Op, +a: Nat, +b: Nat) -> Nat:
  match fuel zero:
    case 0n _:
      0n
    case 1n+_ True{}:
      0n
    case 1n+f False{}:
      +x = Nat.div(a, 2n)
      +y = Nat.div(b, 2n)
      Nat.add(gate(op, Nat.mod(a, 2n), Nat.mod(b, 2n)), Nat.mul(2n, bitwise.go(f, Nat.is_eq(Nat.add(x, y), 0n), op, x, y)))

# a and b bit by bit; a + b is more than the bits it needs.
def bitwise(+op: Op, +a: Nat, +b: Nat) -> Nat:
  bitwise.go(Nat.add(a, b), Nat.is_eq(Nat.add(a, b), 0n), op, a, b)

# base^e modulo l, by squaring, one bit of e at a time.
def power.go(fuel: Nat, zero: Bool, +base: Nat, +e: Nat, +l: Nat) -> Nat:
  match fuel zero:
    case 0n _:
      1n
    case 1n+_ True{}:
      1n
    case 1n+f False{}:
      +h = Nat.div(e, 2n)
      +rest = power.go(f, Nat.is_eq(h, 0n), Nat.mod(Nat.mul(base, base), l), h, l)
      Bool.pick(Nat, Nat.is_eq(Nat.mod(e, 2n), 1n), Nat.mod(Nat.mul(base, rest), l), rest)

def power(+base: Nat, +e: Nat, +l: Nat) -> Nat:
  Nat.mod(power.go(e, Nat.is_eq(e, 0n), Nat.mod(base, l), e, l), l)

# Shifts and signextend match on the range check, so a run computes a
# power of two only when it is below the limit.
def shifted(c: Bool, +n: Nat, +x: Nat) -> Nat:
  match c:
    case True{}:
      Nat.div(x, Nat.pow(2n, n))
    case False{}:
      0n

def lifted(c: Bool, +n: Nat, +x: Nat, +l: Nat) -> Nat:
  match c:
    case True{}:
      Nat.mod(Nat.mul(x, Nat.pow(2n, n)), l)
    case False{}:
      0n

# The low b + 1 bytes of x, with the top one's high bit copied up.
def extended(c: Bool, +b: Nat, +x: Nat, +l: Nat) -> Nat:
  match c:
    case True{}:
      +m = Nat.pow(2n, Nat.mul(8n, 1n+b))
      +low = Nat.mod(x, m)
      Bool.pick(Nat, Nat.is_lt(low, Nat.div(m, 2n)), low, Nat.add(Nat.sub(l, m), low))
    case False{}:
      x

def word.shr(+n: Nat, +x: Nat, +l: Nat) -> Nat:
  shifted(Nat.is_lt(n, width(l)), n, x)

def word.not(+x: Nat, +l: Nat) -> Nat:
  Nat.sub(Nat.sub(l, 1n), x)

# Two's complement: a word from limit / 2 up is negative.
def negative(+x: Nat, +l: Nat) -> Bool:
  Bool.not(Nat.is_lt(x, Nat.div(l, 2n)))

def magnitude(+x: Nat, +l: Nat) -> Nat:
  Bool.pick(Nat, negative(x, l), Nat.sub(l, x), x)

def negate(+x: Nat, +l: Nat) -> Nat:
  Nat.mod(Nat.sub(l, x), l)

def differ(+a: Bool, +b: Bool) -> Bool:
  Bool.pick(Bool, a, Bool.not(b), b)

def op1(op: Op, +a: Nat, +l: Nat) -> Nat:
  match op:
    case IsZero{}:
      bit(Nat.is_eq(a, 0n))
    case Not{}:
      word.not(a, l)
    case _:
      0n

def op2(op: Op, +a: Nat, +b: Nat, +l: Nat) -> Nat:
  match op:
    case Add{}:
      Nat.mod(Nat.add(a, b), l)
    case Sub{}:
      Bool.pick(Nat, Nat.is_lt(a, b), Nat.sub(l, Nat.sub(b, a)), Nat.sub(a, b))
    case Mul{}:
      Nat.mod(Nat.mul(a, b), l)
    case Div{}:
      Bool.pick(Nat, Nat.is_eq(b, 0n), 0n, Nat.div(a, b))
    case SDiv{}:
      +q = Nat.div(magnitude(a, l), magnitude(b, l))
      Bool.pick(Nat, Nat.is_eq(b, 0n), 0n, Bool.pick(Nat, differ(negative(a, l), negative(b, l)), negate(q, l), q))
    case Mod{}:
      Bool.pick(Nat, Nat.is_eq(b, 0n), 0n, Nat.mod(a, b))
    case SMod{}:
      +r = Nat.mod(magnitude(a, l), magnitude(b, l))
      Bool.pick(Nat, Nat.is_eq(b, 0n), 0n, Bool.pick(Nat, negative(a, l), negate(r, l), r))
    case Exp{}:
      power(a, b, l)
    case SignExtend{}:
      extended(Nat.is_lt(a, Nat.sub(Nat.div(width(l), 8n), 1n)), a, b, l)
    case Lt{}:
      bit(Nat.is_lt(a, b))
    case Gt{}:
      bit(Nat.is_lt(b, a))
    case SLt{}:
      +na = negative(a, l)
      Bool.pick(Nat, differ(na, negative(b, l)), bit(na), bit(Nat.is_lt(a, b)))
    case SGt{}:
      +nb = negative(b, l)
      Bool.pick(Nat, differ(negative(a, l), nb), bit(nb), bit(Nat.is_lt(b, a)))
    case Eq{}:
      bit(Nat.is_eq(a, b))
    case And{}:
      bitwise(And{}, a, b)
    case Or{}:
      bitwise(Or{}, a, b)
    case Xor{}:
      bitwise(Xor{}, a, b)
    case Byte{}:
      +bytes = Nat.div(width(l), 8n)
      Bool.pick(Nat, Nat.is_lt(a, bytes), Nat.mod(Nat.div(b, Nat.pow(2n, Nat.mul(8n, Nat.sub(Nat.sub(bytes, 1n), a)))), 256n), 0n)
    case Shl{}:
      lifted(Nat.is_lt(a, width(l)), a, b, l)
    case Shr{}:
      word.shr(a, b, l)
    case Sar{}:
      Bool.pick(Nat, negative(b, l), word.not(word.shr(a, word.not(b, l), l), l), word.shr(a, b, l))
    case _:
      0n

def op3(op: Op, +a: Nat, +b: Nat, +n: Nat) -> Nat:
  match op:
    case AddMod{}:
      Bool.pick(Nat, Nat.is_eq(n, 0n), 0n, Nat.mod(Nat.add(a, b), n))
    case MulMod{}:
      Bool.pick(Nat, Nat.is_eq(n, 0n), 0n, Nat.mod(Nat.mul(a, b), n))
    case _:
      0n

# An operation on its words at the limit l. The reader gives each its
# number of words; any other number gives 0.
def op(+o: Op, args: List<&2, Nat>, +l: Nat) -> Nat:
  match args:
    case a <> Nil{}:
      op1(o, a, l)
    case a <> b <> Nil{}:
      op2(o, a, b, l)
    case a <> b <> c <> Nil{}:
      op3(o, a, b, c)
    case _:
      0n

def info(op: Op) -> Info:
  match op:
    case Add{}:
      Info{"Add", "add", "unchecked.add", 2n}
    case Sub{}:
      Info{"Sub", "sub", "unchecked.sub", 2n}
    case Mul{}:
      Info{"Mul", "mul", "unchecked.mul", 2n}
    case Div{}:
      Info{"Div", "div", "unchecked.div", 2n}
    case SDiv{}:
      Info{"SDiv", "sdiv", "sdiv", 2n}
    case Mod{}:
      Info{"Mod", "mod", "unchecked.mod", 2n}
    case SMod{}:
      Info{"SMod", "smod", "smod", 2n}
    case AddMod{}:
      Info{"AddMod", "addmod", "addmod", 3n}
    case MulMod{}:
      Info{"MulMod", "mulmod", "mulmod", 3n}
    case Exp{}:
      Info{"Exp", "exp", "unchecked.exp", 2n}
    case SignExtend{}:
      Info{"SignExtend", "signextend", "signextend", 2n}
    case Lt{}:
      Info{"Lt", "lt", "lt", 2n}
    case Gt{}:
      Info{"Gt", "gt", "gt", 2n}
    case SLt{}:
      Info{"SLt", "slt", "slt", 2n}
    case SGt{}:
      Info{"SGt", "sgt", "sgt", 2n}
    case Eq{}:
      Info{"Eq", "eq", "eq", 2n}
    case IsZero{}:
      Info{"IsZero", "iszero", "iszero", 1n}
    case And{}:
      Info{"And", "and", "and", 2n}
    case Or{}:
      Info{"Or", "or", "or", 2n}
    case Xor{}:
      Info{"Xor", "xor", "xor", 2n}
    case Not{}:
      Info{"Not", "not", "not", 1n}
    case Byte{}:
      Info{"Byte", "byte", "byte", 2n}
    case Shl{}:
      Info{"Shl", "shl", "shl", 2n}
    case Shr{}:
      Info{"Shr", "shr", "shr", 2n}
    case Sar{}:
      Info{"Sar", "sar", "sar", 2n}

def ops() -> List<&2, Op>:
  [Add{},
  Sub{},
  Mul{},
  Div{},
  SDiv{},
  Mod{},
  SMod{},
  AddMod{},
  MulMod{},
  Exp{},
  SignExtend{},
  Lt{},
  Gt{},
  SLt{},
  SGt{},
  Eq{},
  IsZero{},
  And{},
  Or{},
  Xor{},
  Not{},
  Byte{},
  Shl{},
  Shr{},
  Sar{}]

# The word operations in a contract, such as x : Nat <- Evm.shl(8n, y).
def math(+o: Op, args: List<&2, Nat>) -> Contract(Nat):
  R => k => +s => k(op(o, args, limit.of(s)), s)

def unchecked.add(a: Nat, b: Nat) -> Contract(Nat):
  math(Add{}, [a, b])

def unchecked.sub(a: Nat, b: Nat) -> Contract(Nat):
  math(Sub{}, [a, b])

def unchecked.mul(a: Nat, b: Nat) -> Contract(Nat):
  math(Mul{}, [a, b])

def unchecked.div(a: Nat, b: Nat) -> Contract(Nat):
  math(Div{}, [a, b])

def sdiv(a: Nat, b: Nat) -> Contract(Nat):
  math(SDiv{}, [a, b])

def unchecked.mod(a: Nat, b: Nat) -> Contract(Nat):
  math(Mod{}, [a, b])

def smod(a: Nat, b: Nat) -> Contract(Nat):
  math(SMod{}, [a, b])

def addmod(a: Nat, b: Nat, n: Nat) -> Contract(Nat):
  math(AddMod{}, [a, b, n])

def mulmod(a: Nat, b: Nat, n: Nat) -> Contract(Nat):
  math(MulMod{}, [a, b, n])

def unchecked.exp(base: Nat, e: Nat) -> Contract(Nat):
  math(Exp{}, [base, e])

def signextend(b: Nat, x: Nat) -> Contract(Nat):
  math(SignExtend{}, [b, x])

def lt(a: Nat, b: Nat) -> Contract(Nat):
  math(Lt{}, [a, b])

def gt(a: Nat, b: Nat) -> Contract(Nat):
  math(Gt{}, [a, b])

def slt(a: Nat, b: Nat) -> Contract(Nat):
  math(SLt{}, [a, b])

def sgt(a: Nat, b: Nat) -> Contract(Nat):
  math(SGt{}, [a, b])

def eq(a: Nat, b: Nat) -> Contract(Nat):
  math(Eq{}, [a, b])

def iszero(a: Nat) -> Contract(Nat):
  math(IsZero{}, [a])

def and(a: Nat, b: Nat) -> Contract(Nat):
  math(And{}, [a, b])

def or(a: Nat, b: Nat) -> Contract(Nat):
  math(Or{}, [a, b])

def xor(a: Nat, b: Nat) -> Contract(Nat):
  math(Xor{}, [a, b])

def not(a: Nat) -> Contract(Nat):
  math(Not{}, [a])

def byte(i: Nat, x: Nat) -> Contract(Nat):
  math(Byte{}, [i, x])

def shl(shift: Nat, x: Nat) -> Contract(Nat):
  math(Shl{}, [shift, x])

def shr(shift: Nat, x: Nat) -> Contract(Nat):
  math(Shr{}, [shift, x])

def sar(shift: Nat, x: Nat) -> Contract(Nat):
  math(Sar{}, [shift, x])

# The environment, as in Solidity: block.timestamp is Evm.timestamp(),
# tx.origin is Evm.origin(), address(a).balance is Evm.balance(a), and so on.
def timestamp() -> Contract(Nat):
  env(Timestamp{}, [])

def chainid() -> Contract(Nat):
  env(ChainId{}, [])

def origin() -> Contract(Nat):
  env(Origin{}, [])

def gasprice() -> Contract(Nat):
  env(GasPrice{}, [])

def coinbase() -> Contract(Nat):
  env(Coinbase{}, [])

def number() -> Contract(Nat):
  env(Number{}, [])

def prevrandao() -> Contract(Nat):
  env(PrevRandao{}, [])

def gaslimit() -> Contract(Nat):
  env(GasLimit{}, [])

def basefee() -> Contract(Nat):
  env(BaseFee{}, [])

def blobbasefee() -> Contract(Nat):
  env(BlobBaseFee{}, [])

def blockhash(n: Nat) -> Contract(Nat):
  env(BlockHash{}, [n])

def blobhash(i: Nat) -> Contract(Nat):
  env(BlobHash{}, [i])

def codesize() -> Contract(Nat):
  env(CodeSize{}, [])

def gas() -> Contract(Nat):
  env(Gas{}, [])

def balance(a: Nat) -> Contract(Nat):
  env(Balance{}, [a])

def selfbalance() -> Contract(Nat):
  env(SelfBalance{}, [])

def extcodesize(a: Nat) -> Contract(Nat):
  env(ExtCodeSize{}, [a])

def extcodehash(a: Nat) -> Contract(Nat):
  env(ExtCodeHash{}, [a])

# The wei that the call sent. A callback has its own value, so it is a
# reading. A function that is not payable reverts when it gets ether, so
# there it is zero.
def callvalue() -> Contract(Nat):
  env(CallValue{}, [])
