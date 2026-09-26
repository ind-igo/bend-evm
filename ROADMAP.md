# Roadmap

## M1: the Counter runs on a chain

One real contract, end to end, with a small Yul fragment instead of all of Yul.

```text
counter/program.bend ─ read ─→ IR ─ lower ─→ Yul ─ solc ─→ bytecode ─→ anvil
        │ LAWS (spec)         │ CERT          │ preservation proof
        └──── proved ─────────┴──── proved ───┘
```

### Done when

- [x] `bun vendor/bend-frontend/host/run.js src/compile.bend examples/counter/program.bend get increment set` prints `Counter.yul` with a standard ABI dispatcher for `get()`, `increment()` and `set(uint256)`.
- [x] `solc --strict-assembly` compiles it.
- [x] A test deploys it on `anvil` with real transactions and calls it through the standard ABI:
  - `get()` returns the stored value, and `increment()` adds 1.
  - `set(x)` from the owner (impersonated) writes x. From any other address it reverts.
  - `increment()` at 2^256 − 1 reverts (set with `anvil_setStorageAt`).
  - A call with ETH, or with an unknown selector, reverts.
- [x] Three proof layers check in Bend: the Counter laws (specification), the certificate (contract ≡ IR), and a preservation law for every IR command (running `lower(cmd)` in the Yul model gives the same outcome as `IR.call(cmd)`).
- [x] The README states the boundary: the lowering is proved; the dispatcher, ABI encoding, printer, `solc`, and the match between the Yul model and the EVM are tested.

### Yul fragment

- Statements: `let`, expression statements, `if`, `switch` (dispatcher only), blocks, `revert`, `return`.
- Builtins: `sload`, `sstore`, `caller`, `add`, `sub`, `not`, `gt`, `lt`, `eq`, `iszero`, `calldataload`, `shr`, `callvalue`, `mstore`.

Not in M1: loops, user-defined Yul functions, memory other than the return buffer, mappings, events, payable functions, gas tuning, a proved dispatcher, literals above 2^32 − 1.

### Steps

1. [x] Yul model: AST and evaluator over the `State` of `Evm.bend`, with a symbolic `limit`.
2. [x] `lower : IR.Cmd → Yul` and the preservation law. Checked add lowers to `if gt(b, sub(not(0), a)) { revert(0, 0) }` and a wrapping `add`.
   - [x] 2a: structural proof. The model gives that guard its meaning (a + b ≥ limit) through an `Overflow{a, b}` condition, and its `add` does not wrap, because it only runs after the guard.
   - [x] 2b: the model uses the EVM's `add`, `sub`, `not` and `gt`, and a lemma proves the guard is zero exactly when a + b < limit. Above `limit`, where the EVM has no words, the model picks results that make the guard revert, so no range invariant is needed.
3. [x] Printer and ABI dispatcher: parameters from calldata, results through memory.
4. [x] Keccak-256 in Bend for selectors, tested against `cast sig`.
5. [x] The `anvil` test. `yul-u32/` is deleted, and the frontend's docs point at `src/yul.bend`.

## M2: a minimal token

A token with `totalSupply()`, `balanceOf(address)`, `transfer(address,uint256) returns (bool)` and an owner-only `mint(address,uint256)`. `transfer` and `mint` emit `Transfer`.

### Done when

- [x] `examples/token` compiles, and a test on `anvil` checks every function through the standard ABI, the events included.
- [x] Laws: `transfer` moves exactly `amount` from the caller to the receiver and keeps `totalSupply`; it reverts when the balance is too small; only the owner can mint.
- [x] The preservation proof covers every new IR command, and the certificate covers the token.

Not in M2: `approve` and `transferFrom`, constructor arguments, a law that `totalSupply` is the sum of all balances.

### Steps

1. [x] Checked sub: `if lt(a, b) { revert(0, 0) }`, then `sub(a, b)`.
2. [x] Mappings. Storage keys are data, `Slot{n}` or `Entry{slot, key}`, in the model and the laws (replaced by `Plain` and `Mapped` in M4). `lower` prints `Entry` as `mstore(0, key) mstore(32, slot) keccak256(0, 64)`. The only assumption is that Keccak has no collisions, as in Solidity.
3. [x] `address` parameters. The dispatcher reverts when the upper 96 bits are not zero (tested).
4. [x] Events. The state has a log list, and the outcome includes it, so the proof covers the events. Topics come from Keccak in Bend.
5. [x] The token example, its laws, certificate and `anvil` test. A `bool` result is the word 1, which has the same ABI encoding.

## M3: laws for any state

The M2 laws had fixed addresses and hypotheses such as `a >= amount`. Bend has no holes and no `with`, so each hypothesis had to rewrite a copy of the rest of the program, written out as helper defs.

### Done when

- [x] `Contract` is continuation-passing, so each check is a `Bool.pick` at the top of the normal form.
- [x] The counter and token laws state every outcome from any state: any storage, caller, addresses (a self-transfer too), amounts, limit and logs. Each proof is `{==}`.
- [x] The preservation law holds for every continuation, and the certificates and tests are unchanged.

## M4: the rest of ERC-20

`allowance(address,address)`, `approve(address,uint256) returns (bool)` and `transferFrom(address,address,uint256) returns (bool)`. `approve` emits `Approval`.

### Done when

- [x] Nested mappings: a storage key is `Plain{slot}` or `Mapped{base, key}`, and the printer puts `Mapped` at `keccak256(key . base)`, the Solidity layout. The allowance of `owner` for `spender` is at `keccak256(spender . keccak256(owner . 2))` (tested with `cast index`).
- [x] Laws for any state: `approve` sets the allowance and logs `Approval`; `transferFrom` reverts unless the allowance and the balance cover the amount, and otherwise lowers the allowance and moves the amount.
- [x] The `anvil` test checks the new functions, their events and the storage layout.

Not in M4: the unlimited allowance (`2^256 - 1` is not lowered), which needs branches in contracts.

## M5: select and the unlimited allowance

`Evm.select(cond, a, b)` is `a` when `cond` holds and `b` otherwise, and `Evm.max()` is the largest word, 2^256 − 1. With them, `transferFrom` keeps an allowance of `max()`, as OpenZeppelin does (replaced by solmate's branch in M13).

A full `if`/`else` is not in M5. A branch must pass the continuation to both arms, and functions cannot be copied, so it needs a `match` in a helper def. The checker keeps that match stuck with its arms unapplied, so a law would have to restate the rest of the program. A select only chooses a word, which is `Data`, so laws stay `{==}`.

### Done when

- [x] The IR has `Select{cond, yes, no}` and `Max{}` words. `Select` lowers to a Yul function `select(c, a, b)` in the runtime, and `Max` to `not(0)`. The preservation proof covers both.
- [x] `transferFrom` spends nothing from an allowance of `max()`. The law and the `anvil` test cover it.

## M6: a constructor

An entry named `init` runs at deploy. The token stores the deployer as its owner in slot 3 (slot 4 since M12), and has `owner()` and `transferOwnership(address)`, which emits `OwnershipTransferred`, as OpenZeppelin's `Ownable` does.

### Done when

- [x] `compile.bend` puts `init` in the deploy code, where its final stop falls through to returning the runtime code. It rejects an `init` with parameters (allowed since M9) or a result.
- [x] Log data is a list of words, so an event may have no data, like `OwnershipTransferred`.
- [x] Laws for `init`, `owner` and `transferOwnership`; `mint` checks the stored owner. The `anvil` test deploys from a normal account.

Not in M6: constructor arguments.

## M7: internal calls

A contract function can call the contract's other functions, like `move(from, to, amount)` in the token. The reader inlines each call, so the IR, the lowering and the proof do not change, and the certificate checks the inlining.

### Done when

- [x] The callee's parameters become the argument expressions, and its other levels move above the caller's, so no variable is captured and Yul declares no local twice. A returned value replaces the bound variable; a tail action binds it.
- [x] `transfer` and `transferFrom` share `move`, and `mint` and `move` share `credit` (inlined in M14). The token laws did not change.
- [x] A test inlines each form of call, runs it on `anvil`, and checks that a wrong join gives a certificate that fails.

Not in M7: recursion (calls nest at most 8 deep), and Yul functions for code size.

## M8: a differential test against the model

The token's Bend source is the specification that the laws describe. A test runs it and the compiled token on the same random calls, and compares the results.

### Done when

- [x] A Bend driver ([tests/fixtures/model/token.bend](tests/fixtures/model/token.bend)) runs the token's functions with `Evm.run` on a call sequence, and prints each return or revert and each log.
- [x] [tests/model.test.js](tests/model.test.js) sends the same seeded random sequence to `anvil` and requires the same transcript. `SEED=<n>` runs another sequence. When the printed `lt` has its operands swapped, the test fails (checked by hand).

Not in M8: words at 2^256. The Bend runtime holds words below 2^48, so the model's limit is 2^40, and its `max()` stands for the EVM's 2^256 − 1. token.test.js tests the overflow boundary.

## M9: constructor arguments

`init` may take parameters, like any other entry. The token's `init(supply)` gives the initial supply to the deployer and logs a `Transfer` from zero, as OpenZeppelin's ERC-20 examples do.

### Done when

- [x] The deploy code reverts when fewer ABI words follow it than `init` has parameters, copies them to memory, and reads them before the body runs (the body uses memory for `mapped`). An `address` argument above 2^160 reverts, as in the dispatcher.
- [x] The token law for `init` states the supply, the balance and both logs, for any state, by `{==}`.
- [x] The differential test deploys with a random supply, and a test deploys with 0, 31 and 32 bytes of arguments.

## M10: the total supply is the sum of the balances

The first law over many calls. From deployment, after any list of calls by anyone, `totalSupply` equals the sum of the balances.

### Done when

- [x] `law supply_sum` in [examples/token/LAWS.bend](examples/token/LAWS.bend) states it for any list of accounts that has the deployer and each sender and receiver exactly once, such as the list of every address. It needs no de-duplication of storage keys: each step is a lookup and Nat arithmetic.
- [x] The proof shows what one transfer and one mint do to each balance, sums that over the list, and shows that `approve` and `transferOwnership` write no balance. The proof never uses the limit, so it holds at 2^256.
- [x] With `transfer` changed to credit one more than it debits, the supply proof alone fails (checked by hand, apart from the other laws, which fail too).

Not in M10: view calls in the sequence (they write no storage, as their laws show), and a law that names the sum over all 2^160 addresses directly.

## M11: a usable ERC-20

A token that someone can write, deploy and use from a wallet, after solmate's ERC20.

### Done when

- [x] A constant string entry, such as `name()`, returns its ABI encoding; `Evm.Uint8` and `Evm.Boolean` are words with their ABI types; parameters are range-checked, results are not.
- [x] `src/abi.bend` prints the ABI JSON, and `bun run build --out` writes the Yul, the bytecode and the ABI.
- [x] [lib/ERC20.bend](lib/ERC20.bend) is the base, and the example token uses it. Its laws, including `supply_sum`, still hold; `init` now mints, so its law states the overflow checks.
- [x] The token test deploys the output of `bun run build --out`, reads the name, symbol and decimals with `cast`, and checks the ABI with `cast interface`.
- [x] Holders can `burn`; its law, the supply proof and both chain tests cover it.
- [x] A differential test runs the token and the same token in Solidity with solmate's logic on the same calls, with 256-bit amounts, and requires the same successes, return bytes and logs. When the Solidity reference forgets the unlimited allowance, the test fails (checked by hand).

## M12: permit (EIP-2612)

Solmate's `permit`: an owner approves a spender with a signature, and anyone can send it.

### Done when

- [x] The state has a `World`: the time, the chain id, the contract's address, and tables that stand for `keccak256` and `ecrecover`. Laws hold for every table. Every law and proof that builds a state takes a world, and each call in `supply_sum` runs in its own world.
- [x] The IR has `timestamp`, `chainid`, `self`, `keccak(words)`, `typed(domain, message)` (the EIP-712 digest), `id(text)` and `recover(digest, v, r, s)`, and conditions have `Not`. One lemma shows that a lowered test is 1 exactly when its condition holds, so the preservation proof covers nested conditions.
- [x] `ERC20.permit`, `nonces` and `domain`; the token's laws for them prove by `{==}`, and `supply_sum` covers `permit`.
- [x] The token test signs permits with `cast`: a good one, a replay, an expired one, a wrong signer, and a junk signature for the zero owner. The differential test adds permits to the Solidity reference; when the reference does not use up the nonce, the test fails (checked by hand).

## M13: branches

`select` picks a value, but a contract could not run different effects on each side of a condition. The continuation cannot be copied into both arms. `Evm.branch` picks a whole contract, so the continuation goes to one arm. A branch must be the last step, and both arms run to the end of the call. A join point, where both arms go on to shared code, needs a proof hypothesis that is a function used in both arms, and Bend does not copy functions.

### Done when

- [x] `Evm.branch(A, cond, a, b)` (the type came second until M14) with `Nat` or `Unit` arms, read to `IR.If` and lowered to a Yul `switch`. Certificates prove by `{==}`; a law about a branch uses `Evm.branch.run`.
- [x] The preservation proof covers `If`, nested too. The continuation is erased in the induction, so both arms use it. The lowering test swaps the arms and the proof fails.
- [x] The reader reads the arms only for a branch, rejects a branch or a call to a branching function before the last step, and counts a branch as one level of the 8-deep limit.
- [x] `transferFrom` skips the store for a max allowance, as solmate does; `supply_sum` still holds. `bun run gas` shows 36899 against 36964 for optimized Solidity.

## M14: typed events and a smaller ERC-20 core

An event is declared once, with its field types, like Solidity's `event` line, and emitted like Solidity's `emit`. Bend has no `event` keyword and a Bend function cannot see its own name or parameter types, so an event is a def whose result type marks it and whose body is its log; the reader and the certificate keep the body honest.

### Done when

- [x] `Evm.Event` is the result type of an event def, `Evm.Indexed(A)` marks an indexed parameter, and `Evm.emit(Transfer(from, to, amount))` logs an event. The reader takes only a def written with `Evm.Event`, and makes the signature, the topics and the data from its parameter types and its name; indexed parameters come first, at most three. The certificate proves the body's log equal to the reader's by `{==}`, so a body that disagrees does not build (tests/emit.test.js).
- [x] [lib/ERC20.bend](lib/ERC20.bend) is only the ERC-20 core: named storage slots, the `Transfer` and `Approval` events, the standard functions, and internal `mint` and `burn`, with one helper, `move`. `permit`, `nonces`, `DOMAIN_SEPARATOR` and the owner move to the example token, with their own slots and `OwnershipTransferred` event. The token's laws did not change and still hold.
- [x] `Evm.log` is no longer part of the contract language: contracts log with `Evm.emit`, and `Evm.log` stays as the model's primitive.

Not in M14: custom errors (every revert is `revert(0, 0)`), and event parameter names in the ABI JSON. M15 adds both.

## M15: custom errors

A revert can say why, as with Solidity's `error` and `require(ok, error)`. An error is declared like an event: a def whose result type marks it and whose body is its data. The model keeps the error, so a law states which error a call reverts with, and the certificate and the lowering proof cover it.

### Done when

- [x] `Evm.Error{signature, args}` is the result type of an error def, and `Evm.ensure(ok, error)` reverts with it unless `ok` holds. The model's outcome is `Raise{error}`; `Revert{}` stays for a revert with no data, so the existing laws hold as they were. The reader reads an error def as it reads an event def, with no indexed fields, and the certificate proves the body by `{==}` (tests/emit.test.js).
- [x] `IR.Ensure` lowers to a Yul `if` that stores the selector and the words and reverts with them. The preservation proof covers it; the lowering test replaces it with a plain revert and the proof fails.
- [x] The example token reverts with errors that have OpenZeppelin's names: `OwnableUnauthorizedAccount` in `mint` and `transferOwnership`, and `ERC2612ExpiredSignature` and `ERC2612InvalidSigner` in `permit`. A zero signer gives `ERC2612InvalidSigner(0, owner)`, where OpenZeppelin's `ECDSA.recover` gives `ECDSAInvalidSignature()`. Its laws state each error, and `supply_sum` still holds. The differential test compares the model's errors with the revert data on `anvil`, and the token test checks the full revert data of each error.
- [x] The reader rejects error defs named `Error` or `Panic`, which are Solidity's own. When two event or error defs have one signature but other parameter names, the ABI gives no names, because the IR does not say which def a log or an error came from.
- [x] The ABI lists each error, and events and errors have their parameter names.

Not in M15: errors in the ERC-20 core. It reverts as solmate does, by checked arithmetic with no data; ERC-6093's `ERC20InsufficientBalance` would need a check before each subtraction.

## M16: view calls

A contract can read another contract, as with Solidity's `IERC20(token).balanceOf(who)`. The call is a `staticcall`, so the other contract cannot change any state, and the laws and proofs of contracts that make no calls stay as they are. Calls that write, and reentrancy, are part two.

### Done when

- [x] `Evm.Call{target, signature, args}` is the result type of an interface def, whose first parameter is the target, and `Evm.view(call)` gives the first word that the call returns. The reader reads an interface def as it reads an error def, without the target, and the certificate proves the body by `{==}` (tests/certify.test.js changes the target, an argument and the name).
- [x] The model takes each answer from a list in the `World`, in call order. The answer carries its call, and a view reverts when the list is empty or the call differs, so the certificate checks the target, the name and the words. Since M17 the certificate does not check the parameter types in the signature; see M17. The other contract can read this contract's state, so an answer is not a function of its call, and a list in call order models that. A law about a fixture states both calls and their order.
- [x] `IR.View` lowers to a Yul `View` or, as the last step, an `Answer`, which store the selector and words, make the `staticcall`, and revert when it fails or returns less than a word. The preservation proof covers both; the lowering test changes each and the proof fails.
- [x] On `anvil`, the fixture reads itself as a token, and reverts when the target reverts or has no code (tests/view.test.js). A function that only makes view calls is `view` in the ABI.

Not in M16: calls that write, such as `IERC20(token).transfer(to, amount)`, results other than one word, sending ETH, and passing the called function's revert data on.

## M17: names, not signatures

An event, error or interface def gives only its name, as in `Evm.Log{"Transfer", [from, to], [amount]}`. The types come from the def's parameters, so they are not written twice.

### Done when

- [x] The model's `Log`, `Error` and `Call` hold a name. The IR keeps the full signature for the printer, and `IR.name` gives the model its name, so the certificate checks that the body's name is the def's own (tests/emit.test.js and tests/certify.test.js change a name, and the certificate fails).
- [x] The reader rejects two defs of one kind with one name and other parameter types, which the model could not tell apart (tests/reject.test.js has an event, an error and a call).
- [x] The cost: the certificate checks the name but no longer the parameter types in a signature, which the reader builds from the def. That code and the overload check are now trusted, as the dispatcher's selectors are, and tested on `anvil`. The README states this.
- [x] The token, the ERC20 core, their laws and the fixtures use names. The certificates do not change, and the laws and proofs hold.

Not in M17: a form with no string. Bend cannot see a def's name, and the IR that the certificate compares is plain data, so the name must be a string once.

