import Base

# The contract model. Words are Nat below the state's limit (2^256 on the EVM).
# Storage is an association list: the newest slot wins, missing slots are zero.
# A key is a plain slot or a mapping entry. On the EVM an entry lives at
# keccak256(key . slot), as in Solidity; the model assumes no collisions.
type Key is Data:
  Plain{slot: Nat}
  Mapped{slot: Nat, key: Nat}

def same(a: Key, b: Key) -> Bool:
  match a b:
    case Plain{x} Plain{y}:
      Nat.is_eq(x, y)
    case Mapped{x, k} Mapped{y, j}:
      Bool.and(Nat.is_eq(x, y), Nat.is_eq(k, j))
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

# An event: its signature, such as "Transfer(address,address,uint256)", the
# indexed words after topic 0, and one data word. Topic 0 is the signature's
# Keccak-256, which the printer computes.
type Log is Data:
  Log{event: String, topics: List<&2, Nat>, data: Nat}

# Logs are newest first.
type State is Data:
  State{storage: List<&2, Slot>, caller: Nat, limit: Nat, logs: List<&2, Log>}

# The limit is state, not a constant: a symbolic limit keeps proofs from
# expanding 2^256 as a unary Nat. Laws proved for every limit hold on the EVM.

def storage.of(s: State) -> List<&2, Slot>:
  match s:
    case State{storage, _, _, _}:
      storage

def caller.of(s: State) -> Nat:
  match s:
    case State{_, caller, _, _}:
      caller

def limit.of(s: State) -> Nat:
  match s:
    case State{_, _, limit, _}:
      limit

# A revert discards every state change, so it carries no state.
type Outcome<-A: Data> is Data:
  Ok{value: A, state: State}
  Revert{}

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

def read(+key: Key) -> Contract(Nat):
  R => k => +s => k(lookup(storage.of(s), key), s)

def sload(slot: Nat) -> Contract(Nat):
  read(Plain{slot})

# The value at key in the mapping at slot.
def load(slot: Nat, key: Nat) -> Contract(Nat):
  read(Mapped{slot, key})

def write.go(key: Key, value: Nat, s: State) -> State:
  match s:
    case State{storage, caller, limit, logs}:
      State{Slot{key, value} <> storage, caller, limit, logs}

def write(key: Key, value: Nat) -> Contract(Unit):
  R => k => s => k(Unit{}, write.go(key, value, s))

def sstore(slot: Nat, value: Nat) -> Contract(Unit):
  write(Plain{slot}, value)

def store(slot: Nat, key: Nat, value: Nat) -> Contract(Unit):
  write(Mapped{slot, key}, value)

def caller() -> Contract(Nat):
  R => k => +s => k(caller.of(s), s)

def log.go(event: String, topics: List<&2, Nat>, data: Nat, s: State) -> State:
  match s:
    case State{storage, caller, limit, logs}:
      State{storage, caller, limit, Log{event, topics, data} <> logs}

def log(event: String, topics: List<&2, Nat>, data: Nat) -> Contract(Unit):
  R => k => s => k(Unit{}, log.go(event, topics, data, s))

def require(ok: Bool) -> Contract(Unit):
  R => k => s => Bool.pick(Outcome<R>, ok, k(Unit{}, s), Revert{})

# Checked addition: reverts on overflow, like Solidity 0.8.
def add(+a: Nat, +b: Nat) -> Contract(Nat):
  R => k => +s => Bool.pick(Outcome<R>, Nat.is_lt(Nat.add(a, b), limit.of(s)), k(Nat.add(a, b), s), Revert{})

# Checked subtraction: reverts when a < b, like Solidity 0.8.
def sub(+a: Nat, +b: Nat) -> Contract(Nat):
  R => k => s => Bool.pick(Outcome<R>, Nat.is_lt(a, b), Revert{}, k(Nat.sub(a, b), s))
