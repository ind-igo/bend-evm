# bend-evm

An EVM backend for **Bend 2**, written in Bend. It consumes the checked `Core.Program` from [bend-frontend](https://github.com/ind-igo/bend-frontend).

Contracts are ordinary Bend functions in the `Contract` monad of [Evm.bend](src/Evm.bend). Specifications are laws about them, as in [examples/counter/LAWS.bend](examples/counter/LAWS.bend) and [examples/token/LAWS.bend](examples/token/LAWS.bend).

```text
contract.bend ─ Frontend.check ─ read ─→ IR ─ lower ─→ Yul ─ solc ─→ bytecode
                                          │           │
                  certificate: IR ≡ contract    law: lower preserves every IR command
```

[ROADMAP.md](ROADMAP.md) gives the milestones and their status.

## Write an ERC-20

[lib/ERC20.bend](lib/ERC20.bend) is the ERC-20 core, after solmate's: its storage slots, its `Transfer` and `Approval` events, the standard functions, and internal `mint` and `burn`. A token imports it, gives its name, symbol and decimals, and exposes each function with a one-line def. [examples/token/program.bend](examples/token/program.bend) is a complete token: it adds EIP-2612 `permit` and an owner, who receives the initial supply and can mint; holders can burn.

```bend
import ../../lib/ERC20.bend as ERC20

def name() -> String:
  "Bend Token"

def decimals() -> Evm.Contract(Evm.Uint8):
  Evm.Contract.pure(Nat, 18n)

def transfer(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  ERC20.transfer(to, amount)

def init(+supply: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    ERC20.mint(who, supply)
```

An event is a def whose result type is `Evm.Event`, like Solidity's `event` line; an indexed parameter has the type `Evm.Indexed(...)`. Its body is its log, and `Evm.emit` logs it, like Solidity's `emit`:

```bend
# event Transfer(address indexed from, address indexed to, uint256 amount);
def Transfer(from: Evm.Indexed(Evm.Address), to: Evm.Indexed(Evm.Address), amount: Nat) -> Evm.Event:
  Evm.Log{"Transfer(address,address,uint256)", [from, to], [amount]}

Evm.emit(Transfer(from, to, amount))
```

The reader takes the signature and the topics from the parameter types, and the certificate checks that the body gives the same log, so an event whose body disagrees with its parameters does not build. The def's name is the ABI event name, so `Transfer` and the function `transfer` differ only in case, as in Solidity.

Build it, then deploy the bytecode with the constructor arguments after it:

```sh
bun run build --out build/Token examples/token/program.bend name symbol decimals init owner \
  transferOwnership totalSupply balanceOf transfer mint burn allowance approve transferFrom \
  nonces DOMAIN_SEPARATOR permit
ARGS=$(cast abi-encode "constructor(uint256)" 1000000000000000000000000)
cast send --rpc-url $RPC --private-key $KEY --create "0x$(cat build/Token.bin)${ARGS#0x}"
```

`build` writes the Yul, the bytecode (`.bin`) and the ABI (`.abi.json`) only when the contract's certificate and `PROOF.bend` check; wallets and `cast` read the token through the ABI. A string entry such as `name()` is a constant with no parameters. `Evm.Uint8` and `Evm.Boolean` are words with those ABI types. The dispatcher reverts when a parameter is out of range, but a result goes out as it is, so the function must keep it in range (the model has no check that a compiled check could match); `Evm.Bytes32` is any word, with the ABI type `bytes32`.

## Gas

`bun run gas` ([scripts/gas.js](scripts/gas.js)) runs the same transactions on the token and on the Solidity reference, without and with the solc optimizer (1,000,000 runs, as in solmate), and prints the receipts' `gasUsed`. These numbers include the 21,000 base cost and the calldata cost. They are from solc 0.8.33 on `anvil`:

| | Bend | Bend, optimized | Solidity | Solidity, optimized |
|---|---:|---:|---:|---:|
| deploy | 534212 | 470750 | 1293946 | 873554 |
| mint to a new holder | 70248 | 70243 | 71137 | 70424 |
| mint to a holder | 36048 | 36043 | 36937 | 36224 |
| transfer to a new holder | 51175 | 51140 | 52045 | 51252 |
| transfer to a holder | 34075 | 34040 | 34945 | 34152 |
| approve | 46032 | 46036 | 46685 | 46102 |
| transferFrom, finite allowance | 40012 | 39919 | 41182 | 40087 |
| approve max | 29292 | 29296 | 29945 | 29362 |
| transferFrom, max allowance | 36899 | 36832 | 37908 | 36964 |
| burn | 33538 | 33536 | 34156 | 33604 |
| permit | 73797 | 73836 | 77561 | 74384 |
| runtime code (bytes) | 2071 | 1779 | 5554 | 3639 |

Every transaction of the Bend token uses a little less gas than optimized Solidity. The runtime code is smaller too, although a branch copies the code after it into both arms. `bun run build` does not use the optimizer: it changes little gas, and the tests run the code that is not optimized.

## Use

Requires Git and Bun. The tests also need `solc`, `anvil` and `cast`.

```sh
git submodule update --init --recursive
bun run check   # check every Bend entry point and proof
bun run test
mkdir -p build
bun run build examples/counter/program.bend get increment decrement set > build/Counter.yul
solc --strict-assembly --evm-version shanghai --bin build/Counter.yul
```

[tests/counter.test.js](tests/counter.test.js) and [tests/token.test.js](tests/token.test.js) deploy the examples on `anvil` and call them through the standard ABI. The token's functions are `name symbol decimals init owner transferOwnership totalSupply balanceOf transfer mint burn allowance approve transferFrom nonces DOMAIN_SEPARATOR permit`. An entry named `init` is the constructor: it returns `Unit` and runs in the deploy code, so the deployer is `caller()`. Its parameters are the ABI words that follow the deploy code, as in Solidity; the token's `init(supply)` gives the initial supply to the deployer.

The frontend is a submodule at `vendor/bend-frontend`, and it pins Bend at `vendor/bend-frontend/vendor/bend`. Its `host/run.js` launches the Bend drivers here with the checker attached, and keeps compiled tools in `vendor/bend-frontend/build/cache`. See [Connecting Bend to backends](https://github.com/ind-igo/bend-frontend/blob/main/docs/backends.md) for how a backend uses the frontend, and the frontend's README for what it trusts.

## Certificates

[certify.bend](src/certify.bend) prints each entry as a literal [IR](src/ir.bend) value and a law stating that `IR.call` of that value equals the source function. `IR.call` reverts when a variable is not bound, then runs the IR. The IR constructors map one to one to DSL calls, so both sides normalize to the same term and `{==}` proves the law.

The reader ([read.bend](src/read.bend)) is not trusted: a wrong IR makes the certificate fail. It inlines calls to the contract's own functions with [inline.bend](src/inline.bend), so the certificate also checks the inlining. The trusted base is the Bend checker, the semantics in `Evm.bend` and `ir.bend`, and the shape of the law that certify.bend prints. certify.bend rejects a contract that imports a different `Evm.bend`, and a parameter list that does not bind levels 0, 1, ... in order.

## Lowering

[yul.bend](src/yul.bend) defines the Yul fragment that the IR needs, its meaning over the same `State`, and `lower`. [LAWS.bend](src/LAWS.bend) states that running `lower(cmd)` gives the same outcome as `IR.run(cmd)` for every command, output kind, environment, continuation and state, and [PROOF.bend](src/PROOF.bend) proves it by induction. [compile.bend](src/compile.bend) prints the Yul with an ABI dispatcher, and [keccak.bend](src/keccak.bend) computes the selectors and event topics.

Checked add lowers to `if gt(b, sub(not(0), a)) { revert(0, 0) }` and a wrapping `add`. Checked sub lowers to `if lt(a, b) { revert(0, 0) }` and `sub(a, b)`. `select` lowers to a runtime Yul function `select(c, a, b)`, and `max()` to `not(0)`. The model's `add`, `sub`, `not` and `gt` are the EVM's operations on words below `limit`. Above `limit` the EVM has no words, so the model picks results that keep the proof exact: the add check reverts, and `sub(a, b)` is `a - b` whenever `a ≥ b`. The proof therefore needs no invariant that words stay below `limit`, only the lemma that the check is zero exactly when `a + b < limit`.

Proved: contract ≡ IR (certificate) and IR ≡ Yul model (the law). Tested, not proved: the printer, the dispatcher and ABI decoding, the mapping layout, event topics, `solc`, and the match between the Yul model and the EVM on words below 2^256. [tests/model.test.js](tests/model.test.js) runs random call sequences on the token's Bend source and on `anvil`, and requires the same returns, reverts and logs. The Bend runtime holds words below 2^48 only, so that test uses a limit of 2^40 and small amounts: it does not reach the overflow boundary, which token.test.js tests at 2^256. [tests/reference.test.js](tests/reference.test.js) gives the same random calls, with 256-bit amounts, to the token and to the same token in Solidity with solmate's logic ([tests/fixtures/reference/Token.sol](tests/fixtures/reference/Token.sol)), and requires the same successes, return bytes and logs; only the revert data differs.

The proofs cover deployed code only when the certificate covers the same entries. `compile.bend` reads the IR again and does not check that a `CERT.bend` exists or is current. `bun run build` does it in the right order: it writes `CERT.bend` for the listed functions, checks it and the contract's `PROOF.bend`, and prints the Yul only when both check. The model also has no gas: a law that gives `Ok` holds on chain only when the call has enough gas, and otherwise the call reverts.

## Model

- A contract passes its result and state to a continuation, and `Evm.run(A, m, s)` gives its outcome. Each check is then a `Bool.pick` at the top of the normal form. So a law can state every outcome from any state, with symbolic storage, caller, addresses and amounts, and `{==}` proves it. See the [counter](examples/counter/LAWS.bend) and [token](examples/token/LAWS.bend) laws.
- Laws can also cover many calls. The token's `supply_sum` law runs any list of calls from deployment, with a `Call` for each function that writes storage, and proves that `totalSupply` is the sum of the balances of any list of accounts that has the deployer and each sender and receiver once. The list of every address qualifies, so the supply is the sum of all balances. Its proof is by induction over the calls and the list, with Nat facts from [nat.bend](src/nat.bend).
- A state also has a `World`: the block time, the chain id, the contract's address, and tables that stand for `keccak256` and `ecrecover`. A law holds for every table, so no law depends on how either function works, and the printer uses the real ones: `keccak256` over memory, and the `ecrecover` precompile, which gives zero for a bad signature. `permit` checks that the signer is not zero.
- Words are `Nat`. Checked `add` reverts at the state's `limit`, which is 2^256 on the EVM, and checked `sub` reverts below zero. Proofs keep the limit symbolic: the checker writes any closed Nat near 2^256 out in unary.
- Storage is an association list: the newest slot wins and missing slots read as zero. A key is a plain slot or an entry of a mapping, `Mapped{base, key}`, where `base` is a key too. The printer puts an entry at `keccak256(key . base)`, as Solidity does, so the model assumes that Keccak has no collisions. That is not enough for a slot that a variable gives, which could equal an entry's `keccak256(key . base)`, so `compile.bend` refuses an entry whose plain slots and mapping bases are not literals. Keys can be variables. A revert discards all state.
- `branch(cond, A, a, b)` runs the contract `a` when `cond` holds and `b` otherwise, and must be the last step: each arm runs to the end of the call. Code that both arms run after the choice goes in each arm, as a call to a def, as `ERC20.transferFrom` does with `move`. A run stops at a branch whose condition is not known, so a law about it names both arms with `Evm.branch.run` ([tests/fixtures/branch](tests/fixtures/branch) has examples).
- Events are `emit(Event(...))` with an event def, as above, or `log(signature, topics, data)`: an ABI signature, at most three indexed words and a list of data words, one word for each parameter of the signature. The indexed parameters must come first in the signature (and in an event def), as in `Transfer(address,address,uint256)`: the ABI marks the first parameters as indexed, one for each topic word. The state keeps them newest first, so a revert drops them too. Topic 0 is the signature's Keccak-256, which the printer computes.
- Supported now: `sload`, `sstore`, mappings (`load(slot, key)`, `store(slot, key, value)`) and nested mappings (`load2(slot, outer, inner)`, `store2(slot, outer, inner, value)`), `caller`, checked `add` and `sub`, `select(cond, a, b)`, `branch(cond, A, a, b)`, `max()`, `require`, `log`, `emit`, `pure`, Nat and address parameters, literal constants, and calls to the contract's own functions, which the reader inlines. The reader rejects everything else.

## Limits

- The certificate's imports are relative. Save it as `CERT.bend` beside the contract, or it names other files.
- certify.bend must run through the frontend's `host/run.js`, which gives it its own path in `BEND_ENTRY`.
- Literals are limited by `Nat.read` (about 2^48). Source Nat literals already stop at 2^32 - 1.
- Parameters are `uint256` (`Nat`) or `address` (`Evm.Address`, which is `Nat`); the dispatcher reverts on an address above 2^160. Results are `uint256`; a `bool` result is the word 1 or 0, which has the same encoding.
- Calls and branches nest at most 8 deep together, so a function cannot call itself. An `else if` chain of 8 branches is too deep.
- A branch must be the last step, and its arms return `Nat` or `Unit`. There is no join point after a branch; see ROADMAP.md (M13).
- In the reader, match on `Call` tags, not on nested `Term` patterns or string literals. A string pattern costs the checker 33 splits per character, and each fallback case is copied into every split. Nested Term patterns made checking take 6 GB, and string names made it take 2.5 GB; with tags, `read.bend` checks in about 120 MB. Add a name to `tags()` to read a new DSL call.
