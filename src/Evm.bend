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

# A revert discards every state change, so it carries no state.
type Outcome<-A: Data> is Data:
  Ok{value: A, state: State}
  Revert{}

def Contract(-A: Data) -> Type:
  State -> Outcome<A>

def Contract.pure(-A: Data, x: A) -> Contract(A):
  s => Ok{x, s}

def Contract.next(-A: Data, -B: Data, r: Outcome<A>, f: A -> Contract(B)) -> Outcome<B>:
  match r:
    case Ok{value, state}:
      f(value, state)
    case Revert{}:
      Revert{}

def Contract.bind(-A: Data, -B: Data, m: Contract(A), f: A -> Contract(B)) -> Contract(B):
  s => Contract.next(A, B, m(s), f)

def lookup(storage: List<&2, Slot>, +key: Key) -> Nat:
  match storage:
    case Nil{}:
      0n
    case Slot{k, v} <> rest:
      Bool.pick(Nat, same(k, key), v, lookup(rest, key))

def sload.go(+key: Key, s: State) -> Outcome<Nat>:
  match s:
    case State{+storage, caller, limit, logs}:
      Ok{lookup(storage, key), State{storage, caller, limit, logs}}

def read(key: Key) -> Contract(Nat):
  s => sload.go(key, s)

def sload(slot: Nat) -> Contract(Nat):
  read(Plain{slot})

# The value at key in the mapping at slot.
def load(slot: Nat, key: Nat) -> Contract(Nat):
  read(Mapped{slot, key})

def sstore.go(key: Key, value: Nat, s: State) -> Outcome<Unit>:
  match s:
    case State{storage, caller, limit, logs}:
      Ok{Unit{}, State{Slot{key, value} <> storage, caller, limit, logs}}

def write(key: Key, value: Nat) -> Contract(Unit):
  s => sstore.go(key, value, s)

def sstore(slot: Nat, value: Nat) -> Contract(Unit):
  write(Plain{slot}, value)

def store(slot: Nat, key: Nat, value: Nat) -> Contract(Unit):
  write(Mapped{slot, key}, value)

def caller.go(s: State) -> Outcome<Nat>:
  match s:
    case State{storage, +caller, limit, logs}:
      Ok{caller, State{storage, caller, limit, logs}}

def caller() -> Contract(Nat):
  s => caller.go(s)

def log.go(event: String, topics: List<&2, Nat>, data: Nat, s: State) -> Outcome<Unit>:
  match s:
    case State{storage, caller, limit, logs}:
      Ok{Unit{}, State{storage, caller, limit, Log{event, topics, data} <> logs}}

def log(event: String, topics: List<&2, Nat>, data: Nat) -> Contract(Unit):
  s => log.go(event, topics, data, s)

def require.go(ok: Bool, s: State) -> Outcome<Unit>:
  match ok:
    case True{}:
      Ok{Unit{}, s}
    case False{}:
      Revert{}

def require(ok: Bool) -> Contract(Unit):
  s => require.go(ok, s)

# A checked result: the value when ok, a revert otherwise.
def checked(+value: Nat, ok: Bool, s: State) -> Outcome<Nat>:
  match ok:
    case True{}:
      Ok{value, s}
    case False{}:
      Revert{}

def add.sum(+sum: Nat, s: State) -> Outcome<Nat>:
  match s:
    case State{storage, caller, +limit, logs}:
      checked(sum, Nat.is_lt(sum, limit), State{storage, caller, limit, logs})

# Checked addition: reverts on overflow, like Solidity 0.8.
def add(a: Nat, b: Nat) -> Contract(Nat):
  s => add.sum(Nat.add(a, b), s)

# Checked subtraction: reverts when b > a, like Solidity 0.8.
def sub(+a: Nat, +b: Nat) -> Contract(Nat):
  s => checked(Nat.sub(a, b), Bool.not(Nat.is_lt(a, b)), s)
