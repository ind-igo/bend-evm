# bend-evm

An EVM backend for **Bend 2**, written in Bend. It consumes the checked `Core.Program` from [bend-frontend](https://github.com/ind-igo/bend-frontend).

Contracts are ordinary Bend functions in the `Contract` monad of [Evm.bend](src/Evm.bend). Specifications are laws about them, as in [examples/counter/LAWS.bend](examples/counter/LAWS.bend), [examples/erc20/LAWS.bend](examples/erc20/LAWS.bend), [examples/amm/LAWS.bend](examples/amm/LAWS.bend) and [examples/weth/LAWS.bend](examples/weth/LAWS.bend).

```text
contract.bend ─ Frontend.check ─ read ─→ IR ─ lower ─→ Yul ─ solc ─→ bytecode
                                          │           │
                  certificate: IR ≡ contract    law: lower preserves every IR command
```

[ROADMAP.md](ROADMAP.md) gives the milestones and their status.

## Write an ERC-20

[examples/erc20](examples/erc20) has an ERC-20. [ERC20.bend](examples/erc20/ERC20.bend) is the core, after solmate's: its storage slots, its `Transfer` and `Approval` events, the standard functions, and internal `mint` and `burn`. A token imports it, gives its name, symbol and decimals, and exposes each function with a one-line def. [Token.bend](examples/erc20/Token.bend) is a complete token on it: it adds EIP-2612 `permit` and an owner, who receives the initial supply and can mint; holders can burn.

```bend
import ./ERC20.bend as ERC20

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

[LAWS.bend](examples/erc20/LAWS.bend) has the core's laws first, as `core.transfer`, `core.mint` and so on, then the token's. Each core law gives the outcome of a core function from any state, with any continuation: the rest of the token's function, or the end of the call. So a token proves the law for its own function from them, whatever it does before or after. The core's supply laws give the writes that keep the total supply equal to the sum of the balances: each of the core's writes, and each write to a token's own slots. The token's `supply_sum` law follows from them. [PROOF.bend](examples/erc20/PROOF.bend) proves both. Another contract that uses the core's laws imports that `PROOF.bend` too, as Bend refuses a law with no proof.

An event is a def whose result type is `Evm.Log`, like Solidity's `event` line; an indexed parameter has the type `Evm.Indexed(...)`. Its body is its log, and `Evm.emit` logs it, like Solidity's `emit`:

```bend
# event Transfer(address indexed from, address indexed to, uint256 amount);
def Transfer(from: Evm.Indexed(Evm.Address), to: Evm.Indexed(Evm.Address), amount: Nat) -> Evm.Log:
  Evm.Log{"Transfer", [from, to], [amount]}

Evm.emit(Transfer(from, to, amount))
```

The body gives the name, and the reader builds the signature, `Transfer(address,address,uint256)`, from the name and the parameter types, and the topics from `Evm.Indexed`. The certificate checks that the body gives the same log, so an event whose body has another name or other words does not build. The name must be a string because Bend cannot see a def's name, and `Evm.Address` is `Nat` inside Bend, so only the reader can tell the types apart. The model knows an event, error or call by its name, so the reader rejects two defs of one kind with one name and other parameter types: there are no overloads. The def's name is the ABI event name, so `Transfer` and the function `transfer` differ only in case, as in Solidity.

A custom error is a def whose result type is `Evm.Error`, like Solidity's `error` line. Its body is its name and its argument words, and `Evm.ensure(ok, error)` reverts with it unless `ok` holds, like Solidity's `require(ok, error)`:

```bend
# error OwnableUnauthorizedAccount(address account);
def OwnableUnauthorizedAccount(account: Evm.Address) -> Evm.Error:
  Evm.Error{"OwnableUnauthorizedAccount", [account]}

Evm.ensure(Nat.is_eq(who, boss), OwnableUnauthorizedAccount(who))
```

The revert data is the error's selector and its ABI-encoded words, as in Solidity, and the certificate checks the body as it checks an event's. `Evm.require(ok)` reverts with no data. A law states which error a call reverts with: the model's outcome is `Evm.Raise{error}` for a custom error, and `Evm.Revert{}` for a revert with no data.

A contract reads another contract with `Evm.view`, as Solidity's `IERC20(token).balanceOf(who)` does. An interface def gives the call: its first parameter is the target's address, its body is the target, the name and the argument words, and the reader builds the signature from the name and the other parameter types:

```bend
def balanceOf(token: Evm.Address, who: Evm.Address) -> Evm.Call:
  Evm.Call{token, "balanceOf", [who]}

+held : Nat <- Evm.view(balanceOf(token, who))
```

`view` makes a `staticcall` and gives the first word that the function returns, so the called contract cannot change state. The model does not know the other contract: the `World` has a list of answers, and each view takes the next one, or reverts if the list is empty or the answer is for another call. A law holds for every list, so it holds for any contract at the target, even one that reads this contract's state back ([tests/fixtures/view](tests/fixtures/view) has a law).

A call that may write, such as `IERC20(token).transfer(to, amount)`, uses `Evm.call` with the same interface defs:

```bend
ok : Nat <- Evm.call(transfer(token, to, amount))
Evm.require(Nat.is_eq(ok, 1n))
```

`call` makes a `call` with no value and gives the first word that the function returns. The called contract can call back into this one while the call runs, and nothing stops that. The model states it: the contract stops at the call, and [calls.bend](src/calls.bend) runs it with a list of answers. An answer gives the callbacks that the called contract makes into this one, each a call to one of this contract's entries from any sender, with its own answers, and then the word that the call returns. A callback that reverts changes nothing, as the caller may catch it. `Calls.run(Cert.entry.table(), A, m, answers, state)` gives the outcome; `Cert.entry.table()` is the table of the contract's entries in its certificate. A law holds for every list, so it holds for every called contract, including one that calls back. A law can say exactly what the callbacks see: the vault's `deposit` law ([tests/fixtures/vault](tests/fixtures/vault)) shows that they run on the state with the new shares. A law can also hold across every callback: the vault's `shares_sum` law proves that any callbacks, at any depth and from any listed senders, keep the total equal to the sum of the shares, and the `callbacks` law in [LAWS.bend](src/LAWS.bend) carries such a law to the compiled entries. Checks before the call, such as checked arithmetic, stop the run at a pick that it cannot pass, so such a law takes the checks' results as hypotheses.

Build it, then deploy the bytecode with the constructor arguments after it. An entry named `init` is the constructor: it returns `Unit` and runs in the deploy code, so the deployer is `caller()`, and its parameters are the ABI words after the deploy code, as in Solidity.

```sh
bun run build --out build/Token examples/erc20/Token.bend name symbol decimals init owner \
  transferOwnership totalSupply balanceOf transfer mint burn allowance approve transferFrom \
  nonces DOMAIN_SEPARATOR permit
ARGS=$(cast abi-encode "constructor(uint256)" 1000000000000000000000000)
cast send --rpc-url $RPC --private-key $KEY --create "0x$(cat build/Token.bin)${ARGS#0x}"
```

`build` writes the certificate `CERT.bend` for the listed entries, checks it and the contract's `PROOF.bend`, and only then writes the Yul, the bytecode (`.bin`) and the ABI (`.abi.json`); wallets and `cast` read the token through the ABI.

### ABI types

Every word is a `Nat`. These aliases give it an ABI type:

| Bend | ABI | A parameter reverts when |
|---|---|---|
| `Nat` | `uint256` | never |
| `Evm.Address` | `address` | it is 2^160 or more |
| `Evm.Uint8` | `uint8` | it is above 255 |
| `Evm.Boolean` | `bool` | it is above 1 |
| `Evm.Bytes32` | `bytes32` | never |
| `Evm.Int` | `int256` | never |

The dispatcher checks parameters only. A result, an event field or an error argument goes out as it is, so the function must keep it in range, or the output is not a valid ABI encoding. A result of `Unit` has no outputs. A string entry, such as `name()`, is a def with no parameters whose body is a text literal; it returns the ABI encoding of a `string`.

### Arithmetic

`Evm.add`, `Evm.sub` and `Evm.mul` are checked, as in Solidity 0.8: they revert on overflow or below zero. `Evm.div` and `Evm.mod` revert when the divisor is zero. Each takes two words and gives one, as a step:

```bend
# Uniswap V2's getAmountOut, with the 0.3% fee.
def amountOut(amountIn: Nat, reserveIn: Nat, reserveOut: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +withFee : Nat <- Evm.mul(amountIn, 997n)
    numerator : Nat <- Evm.mul(withFee, reserveOut)
    scaled : Nat <- Evm.mul(reserveIn, 1000n)
    denominator : Nat <- Evm.add(scaled, withFee)
    Evm.div(numerator, denominator)
```

Every other arithmetic, comparison and bitwise opcode is a word operation that never reverts and computes what the EVM computes, modulo 2^256: `Evm.sdiv`, `Evm.smod`, `Evm.addmod`, `Evm.mulmod`, `Evm.signextend`, `Evm.lt`, `Evm.gt`, `Evm.slt`, `Evm.sgt`, `Evm.eq`, `Evm.iszero`, `Evm.and`, `Evm.or`, `Evm.xor`, `Evm.not`, `Evm.byte`, `Evm.shl`, `Evm.shr` and `Evm.sar`. The opcodes that Solidity checks are `Evm.unchecked.add`, `sub`, `mul`, `div`, `mod` and `exp`, as in an `unchecked` block. The words go in Yul's order, so a shift takes the shift first: `Evm.shl(8n, x)`. As on the EVM, a division by zero gives 0, and so do `addmod` and `mulmod` with a modulus of zero, where Solidity reverts. A comparison gives the word 1 or 0. The signed operations read a word as two's complement; `Evm.Int` gives it the ABI type `int256`.

## An AMM

[examples/amm](examples/amm) has a constant-product pair, after Uniswap V2's `UniswapV2Pair`, with the 0.3% fee. [Pair.bend](examples/amm/Pair.bend) uses the ERC-20 core as its liquidity token, calls its two tokens through the defs in [IERC20.bend](examples/amm/IERC20.bend), and takes the square root with solady's method, which has no loop ([Math.bend](examples/amm/Math.bend)). As in Uniswap, a user first sends tokens to the pair, then calls `mint` or `swap`. For `burn`, the user first sends liquidity tokens to the pair.

It differs from Uniswap's pair in these ways. It has no lock, no price oracle, no flash swaps, no `skim` and no protocol fee. The reserves are full words, and `reserve0()` and `reserve1()` replace `getReserves()`. `burn` returns nothing, and the `Burn` event gives the amounts. The errors are custom errors with the names of Uniswap's messages. The indexed event parameters come first, so `Burn` and `Swap` have other signatures. A swap always makes both transfers, also for zero.

[LAWS.bend](examples/amm/LAWS.bend) has these laws, and [PROOF.bend](examples/amm/PROOF.bend) proves them:

- `swap`: a swap does not make x·y go down. This holds for every answer that the two tokens give and for every callback that they make into the pair while it pays, at any depth, with no lock. A swap reads the reserves before it pays, checks the balances after it against them, and then writes those balances as the reserves. So what the callbacks do cannot get past the check. A swap in a callback can use the same tokens in as the swap that it is in, as both check the same balances; x·y still does not go down.
- `mint`: a mint into a pair that has liquidity does not dilute it. For each token, `supply' * reserve <= supply * reserve'`.
- `burn`: a burn pays each token no more than the burned share of the pair's balance, whatever the tokens and their callbacks do.
- `sync`: the balances that the tokens report become the reserves.

The liquidity token's functions are the ERC-20 core's, so the core's laws apply to them. Each proof splits a check with a Bool parameter, and a call with a lemma that takes the rest of the run from any state. [tests/amm.test.js](tests/amm.test.js) gives the pair and the same pair in Solidity ([tests/fixtures/reference/Pair.sol](tests/fixtures/reference/Pair.sol)) the same random steps on `anvil`, with tokens that return false, revert, or call back into the pair with `sync`, `swap` or `mint`.

## Wrapped ether

[examples/weth](examples/weth) has wrapped ether, after solmate's `WETH`, on the ERC-20 core. It shows how a contract takes and sends ether:

```bend
def deposit() -> Evm.Payable(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    +amount : Nat <- Evm.callvalue()
    ERC20.mint(who, amount)
    Evm.emit(Deposit(who, amount))

def withdraw(+amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    ERC20.burn(who, amount)
    Evm.emit(Withdrawal(who, amount))
    Evm.pay(who, amount)
```

- A function whose result type is `Evm.Payable(A)` accepts ether, and the ABI marks it `payable`. Every other function reverts when it gets ether, as in Solidity. `init` can be payable too.
- An entry named `receive` runs when the calldata is empty, as Solidity's `receive()`. It must be payable, take no parameters and return `Unit`.
- `Evm.callvalue()` gives the wei that the call sent. A callback has its own value, so the model takes it from the readings, as it takes `gas`.
- `Evm.pay(to, amount)` sends ether with `call` and no data, and reverts when the call fails. The receiver can call back, so the model stops there, as at `Evm.call`.

[LAWS.bend](examples/weth/LAWS.bend) has three laws: `deposit` and `receive` give the sender as many tokens as the wei sent, and `withdraw` burns the tokens and logs before it pays, with the pay as its last step, so a callback sees the burned balance. [tests/weth.test.js](tests/weth.test.js) gives it and solmate's WETH in Solidity ([tests/fixtures/reference/WETH.sol](tests/fixtures/reference/WETH.sol)) the same random steps on `anvil`, with a holder that refuses ether, or deposits or withdraws again when it gets ether.

The model has no ether balances: `balance` and `selfbalance` are readings. So a law cannot say that WETH holds as much ether as its supply.

## Gas

`bun run gas` ([scripts/gas.js](scripts/gas.js)) runs the same transactions on the token and on the Solidity reference, without and with the solc optimizer (1,000,000 runs, as in solmate), and prints the receipts' `gasUsed`. These numbers include the 21,000 base cost and the calldata cost. They are from solc 0.8.33 for the Cancun EVM on `anvil`:

| | Bend | Bend, optimized | Solidity | Solidity, optimized |
|---|---:|---:|---:|---:|
| deploy | 553029 | 484374 | 1288335 | 868800 |
| mint to a new holder | 70253 | 70243 | 71137 | 70424 |
| mint to a holder | 36053 | 36043 | 36937 | 36224 |
| transfer to a new holder | 51175 | 51140 | 52045 | 51252 |
| transfer to a holder | 34075 | 34040 | 34945 | 34152 |
| approve | 46032 | 46036 | 46685 | 46102 |
| transferFrom, finite allowance | 40012 | 39919 | 41182 | 40087 |
| approve max | 29292 | 29296 | 29945 | 29362 |
| transferFrom, max allowance | 36899 | 36832 | 37908 | 36964 |
| burn | 33538 | 33536 | 34156 | 33604 |
| permit | 73790 | 73841 | 77585 | 74384 |
| runtime code (bytes) | 2158 | 1842 | 5528 | 3617 |

Every transaction of the Bend token uses a little less gas than optimized Solidity. The runtime code is smaller too, although a branch copies the code after it into both arms. The Bend token reverts with custom errors, and the Solidity reference with no data. `bun run build` does not use the optimizer: it changes little gas, and the tests run the code that is not optimized.

## Use

Requires Git and Bun. `bun run build --out` also needs `solc`, and the tests and `bun run gas` need `solc`, `anvil` and `cast`.

```sh
git submodule update --init --recursive
bun run check   # check every proof, certificate and Bend tool
bun run test
mkdir -p build
bun run build examples/counter/program.bend get increment decrement set > build/Counter.yul
solc --strict-assembly --evm-version cancun --bin build/Counter.yul
```

[tests/counter.test.js](tests/counter.test.js) and [tests/token.test.js](tests/token.test.js) deploy the examples on `anvil` and call them through the standard ABI. [scripts/tools.js](scripts/tools.js) holds what the scripts and tests share, including each example's entry list.

The frontend is a submodule at `vendor/bend-frontend`, and it pins Bend at `vendor/bend-frontend/vendor/bend`. Its `host/run.js` launches the Bend drivers here with the checker attached, and keeps compiled tools in `vendor/bend-frontend/build/cache`. See [Connecting Bend to backends](https://github.com/ind-igo/bend-frontend/blob/main/docs/backends.md) for how a backend uses the frontend, and the frontend's README for what it trusts.

## Certificates

[certify.bend](src/certify.bend) prints each entry as a literal [IR](src/ir.bend) value and a law stating that `IR.call` of that value equals the source function. `IR.call` reverts when a variable is not bound, then runs the IR. The IR constructors map one to one to DSL calls, so both sides normalize to the same term and `{==}` proves the law.

The reader ([read.bend](src/read.bend)) is not trusted: a wrong IR makes the certificate fail. There is one exception. The model knows an event, error or call by its name, so the certificate checks the name in a signature but not the parameter types. The reader builds those types from the def, and they give the selector and topic 0. So that code, and the check that rejects two defs of one kind with one name and other types, are trusted as the dispatcher's selectors are; the tests on `anvil` compare them. It inlines calls to the contract's own functions with [inline.bend](src/inline.bend), so the certificate also checks the inlining. The trusted base is the Bend checker, the semantics in `Evm.bend`, `ir.bend` and `calls.bend`, and the shape of the law that certify.bend prints. The tools ([tool.bend](src/tool.bend)) reject a contract that imports a different `Evm.bend`, and the reader rejects a parameter list that does not bind levels 0, 1, ... in order.

## Lowering

[yul.bend](src/yul.bend) defines the Yul fragment that the IR needs, its meaning over the same `State`, and `lower`. [LAWS.bend](src/LAWS.bend) states that running `lower(cmd)` gives the same outcome as `IR.run(cmd)` for every command, output kind, environment, continuation and state, and for every list of answers and callbacks, where the callbacks run the lowered entries on one side and their IR on the other. [PROOF.bend](src/PROOF.bend) proves it by induction on the command, then on the answers. [compile.bend](src/compile.bend) prints the Yul with an ABI dispatcher, and [keccak.bend](src/keccak.bend) computes the selectors and event topics.

Checked add lowers to `if gt(b, sub(not(0), a)) { revert(0, 0) }` and a wrapping `add`. Checked sub lowers to `if lt(a, b) { revert(0, 0) }` and `sub(a, b)`. Checked mul lowers to Solidity's check, `if and(iszero(iszero(a)), gt(b, div(not(0), a))) { revert(0, 0) }`, and `mul(a, b)`; checked div and mod lower to `if iszero(b) { revert(0, 0) }` and `div` or `mod`. A word operation lowers to its opcode. The IR and the Yul model give each word operation the same meaning (`Evm.op`), so one case of the proof covers them all. That meaning takes a word's width from `limit`, so it is each opcode at 2^256, and the same opcode on smaller words at a smaller limit. An `ensure` lowers to an `if` that stores the error's selector and words and reverts with them. A `view` stores the selector and words at memory 0, makes a `staticcall` that writes the result to 0, and reverts with no data if the call fails or `returndatasize()` is less than 32; a `call` does the same with `call`. A callback runs in a new frame with its own memory. `select` lowers to a runtime Yul function `select(c, a, b)`, and `max()` to `not(0)`. The model's `add`, `sub`, `not` and `gt` are the EVM's operations on words below `limit`. Above `limit` the EVM has no words, so the model picks results that keep the proof exact: the add check reverts, and `sub(a, b)` is `a - b` whenever `a ≥ b`. The proof therefore needs no invariant that words stay below `limit`, only the lemma that the check is zero exactly when `a + b < limit`. The mul check is zero exactly when `a * b < limit`, by the floor lemma in [nat.bend](src/nat.bend) (`b ≤ p / a` exactly when `a * b ≤ p`); at the limit 0, where there are no words, the model's `and` gives 1 so that the check reverts.

Proved: contract ≡ IR (certificate) and IR ≡ Yul model (the law). Tested, not proved: the printer, the dispatcher and ABI decoding, the mapping layout, the parameter types in the signatures of events, errors and calls (so their selectors and topics), the encoding of error data and of calls, the entry table for callbacks (the dispatcher must send each selector to the entry of the same name, and the table must list every entry but `init` and the constants, which change nothing), `solc`, and the match between the Yul model and the EVM on words below 2^256. [tests/model.test.js](tests/model.test.js) runs random call sequences on the token's Bend source and on `anvil`, and requires the same returns, reverts, custom errors and logs. The Bend runtime holds words below 2^48 only, so that test uses a limit of 2^40 and small amounts: it does not reach the overflow boundary, which token.test.js tests at 2^256. [tests/callbacks.test.js](tests/callbacks.test.js) sends random transactions to the vault on `anvil`, over a token that calls back in many ways, takes each transaction's answers and callbacks from `anvil`'s call trace, runs the vault's certified entries with them through `calls.bend`, and requires the same result and shares after each transaction; so it tests the model of callbacks, reverts and the caller, and the entry table, against the EVM. [tests/math.test.js](tests/math.test.js) checks every word operation on edge and random words against a reference written from the Yellow Paper ([tests/evm.js](tests/evm.js)), at any width: the model's meaning at 24 bits, as the Bend runtime holds only words below 2^48, and the compiled operations on `anvil` at 256 bits, checked mul, div and mod and the AMM's square root included. [tests/reference.test.js](tests/reference.test.js) gives the same random calls, with 256-bit amounts, to the token and to the same token in Solidity with solmate's logic ([tests/fixtures/reference/Token.sol](tests/fixtures/reference/Token.sol)), and requires the same successes, return bytes and logs; only the revert data differs.

The proofs cover deployed code only when the certificate covers the same entries. `compile.bend` reads the IR again and does not check that a `CERT.bend` exists or is current, so build with `bun run build`, which does. The model also has no gas: a law that gives `Ok` holds on chain only when the call has enough gas, and otherwise the call reverts.

## Model

- A contract passes its result and state to a continuation, and `Evm.run(A, m, s)` gives its outcome. Each check is then a `Bool.pick` at the top of the normal form. So a law can state every outcome from any state, with symbolic storage, caller, addresses and amounts, and `{==}` proves it. See the [counter](examples/counter/LAWS.bend) and [ERC-20](examples/erc20/LAWS.bend) laws.
- Laws can also cover many calls. The token's `supply_sum` law runs any list of calls from deployment, with a `Call` for each function that writes storage, and proves that `totalSupply` is the sum of the balances of any list of accounts that has the deployer and each sender and receiver once. The list of every address qualifies, so the supply is the sum of all balances. Its proof is by induction over the calls and the list, with Nat facts from [nat.bend](src/nat.bend) and the ERC20 core's supply laws. [sum.bend](src/sum.bend) has the facts about a sum over a mapping that such a law needs.
- A state also has a `World`: a table of the values of the environment that are fixed in a transaction, a list of readings for the ones that can change, the contract's address, tables that stand for `keccak256` and `ecrecover`, and the answers of view calls in order. A law holds for every table, so no law depends on how either function works, and the printer uses the real ones: `keccak256` over memory, and the `ecrecover` precompile, which gives zero for a bad signature. `permit` checks that the signer is not zero.
- A value of the environment that is fixed in a transaction, such as `number` or `chainid`, comes from the table, so two reads give the same word (the law `fixed` in [src/LAWS.bend](src/LAWS.bend)). One that can change, such as `gas`, `selfbalance` or `balance(a)`, comes from the next reading, so no law depends on two reads being the same. A missing entry or reading reads as zero. [tests/env.test.js](tests/env.test.js) compares each value with what `anvil` gives.
- A contract that makes calls that may write runs with `Calls.run`, which takes the answers and callbacks as above. A callback names an entry by its index in the certificate's table: the listed entries in order, without `init` and the constants. The EVM rejects some callbacks before an entry runs, such as ones with a bad selector or a bad argument; they change nothing, so a real run has a list without them.
- Words are `Nat`. Checked `add` and `mul` revert at the state's `limit`, which is 2^256 on the EVM, and checked `sub` reverts below zero. The word operations compute modulo `limit`. Proofs keep the limit symbolic: the checker writes any closed Nat near 2^256 out in unary.
- Transient storage (EIP-1153) is in the same list, with keys `Transient{slot}` that never equal a storage key. The EVM clears it at the end of each transaction, and the model does not: a law about one call holds for any transient values at its start, which callbacks need, but a law about a sequence of transactions must clear them itself. [tests/fixtures/transient](tests/fixtures/transient) has a reentrancy guard with two laws: a callback into the guarded function reverts while its call runs.
- Storage is an association list: the newest slot wins and missing slots read as zero. A key is a plain slot or an entry of a mapping, `Mapped{base, key}`, where `base` is a key too. The printer puts an entry at `keccak256(key . base)`, as Solidity does, so the model assumes that Keccak has no collisions. That is not enough for a slot that a variable gives, which could equal an entry's `keccak256(key . base)`, so `compile.bend` refuses an entry whose plain slots and mapping bases are not literals. Keys can be variables. A revert discards all state.
- `branch(A, cond, a, b)` runs the contract `a` when `cond` holds and `b` otherwise, and must be the last step: each arm runs to the end of the call. Code that both arms run after the choice goes in each arm, as a call to a def, as `ERC20.transferFrom` does with `move`. A run stops at a branch whose condition is not known, so a law about it names both arms with `Evm.branch.run` ([tests/fixtures/branch](tests/fixtures/branch) has examples).
- Events are `emit(Event(...))` with an event def, as above: at most three indexed parameters, before the others, as the ABI marks the first parameters as indexed, one for each topic word. The state keeps logs newest first, so a revert drops them too. Topic 0 is the Keccak-256 of the signature, which the printer computes. Two events with the same signature must agree on their indexed parameters.
- Supported now: `sload`, `sstore`, mappings (`load(slot, key)`, `store(slot, key, value)`) and nested mappings (`load2(slot, outer, inner)`, `store2(slot, outer, inner, value)`); transient storage (`tload(slot)`, `tstore(slot, value)`); `caller` and `self`; the environment: `timestamp`, `chainid`, `origin`, `gasprice`, `coinbase`, `number`, `prevrandao`, `gaslimit`, `basefee`, `blobbasefee`, `blockhash(n)`, `blobhash(i)`, `codesize`, `gas`, `balance(a)`, `selfbalance`, `extcodesize(a)` and `extcodehash(a)`; checked `add`, `sub`, `mul`, `div` and `mod`; the word operations; `max()`; `select(cond, a, b)` and `branch(A, cond, a, b)`, where a condition is `Nat.is_eq` or `Nat.is_lt` under `Bool.not`; `require`; `ensure(cond, error)`; `emit`; `view(call)` and `call(call)`; `pay(to, amount)` and `callvalue()`, with `Evm.Payable(A)` results and `receive`; `keccak(words)`, `id(text)`, `typed(domain, message)` (the EIP-712 digest) and `recover(digest, v, r, s)`; `pure`; the parameter types above; literal constants; and calls to the contract's own functions, which the reader inlines. The reader rejects everything else.

## Limits

- The certificate's imports are relative. Save it as `CERT.bend` beside the contract, or it names other files.
- certify.bend must run through the frontend's `host/run.js`, which gives it its own path in `BEND_ENTRY`.
- Literals are limited by `Nat.read` (about 2^48). Source Nat literals already stop at 2^32 - 1.
- Parameters, results, event fields and error arguments are words with the ABI types above; only parameters are range-checked.
- A view or a call gives one word, with no range check, and reverts with no data when the called function fails; Solidity passes on its revert data. `Evm.call` sends no ether; `Evm.pay` sends ether with no data.
- Nothing stops a callback. A law states what callbacks can do, and an invariant across every callback is proved by hand, by induction on the answers, with one lemma for each entry (see the vault's proof). A law about one call needs no induction when it holds for any state that the callbacks leave, as the AMM's `swap` law does. There is no reentrancy guard yet. While a call runs, the called contract can also read this contract's state, so update the state before the call.
- Calls and branches nest at most 8 deep together, so a function cannot call itself. An `else if` chain of 8 branches is too deep.
- A branch must be the last step, and its arms return `Nat` or `Unit`. There is no join point after a branch; see ROADMAP.md (M13).
- In the reader, match on `Call` tags, not on nested `Term` patterns or string literals. A string pattern costs the checker 33 splits per character, and each fallback case is copied into every split. Nested Term patterns made checking take 6 GB, and string names made it take 2.5 GB; with tags, `read.bend` checks in about 120 MB. Add a name to `tags()` to read a new DSL call.
