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
2. [x] Mappings. Storage keys are data, `Slot{n}` or `Entry{slot, key}`, in the model and the laws. `lower` prints `Entry` as `mstore(0, key) mstore(32, slot) keccak256(0, 64)`. The only assumption is that Keccak has no collisions, as in Solidity.
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

`Evm.select(cond, a, b)` is `a` when `cond` holds and `b` otherwise, and `Evm.max()` is the largest word, 2^256 − 1. With them, `transferFrom` keeps an allowance of `max()`, as OpenZeppelin does.

A full `if`/`else` is not in M5. A branch must pass the continuation to both arms, and functions cannot be copied, so it needs a `match` in a helper def. The checker keeps that match stuck with its arms unapplied, so a law would have to restate the rest of the program. A select only chooses a word, which is `Data`, so laws stay `{==}`.

### Done when

- [x] The IR has `Select{cond, yes, no}` and `Max{}` words. `Select` lowers to a Yul function `select(c, a, b)` in the runtime, and `Max` to `not(0)`. The preservation proof covers both.
- [x] `transferFrom` spends nothing from an allowance of `max()`. The law and the `anvil` test cover it.

## M6: a constructor

An entry named `init` runs at deploy. The token stores the deployer as its owner in slot 3, and has `owner()` and `transferOwnership(address)`, which emits `OwnershipTransferred`, as OpenZeppelin's `Ownable` does.

### Done when

- [x] `compile.bend` puts `init` in the deploy code, where its final stop falls through to returning the runtime code. It rejects an `init` with parameters or a result.
- [x] Log data is a list of words, so an event may have no data, like `OwnershipTransferred`.
- [x] Laws for `init`, `owner` and `transferOwnership`; `mint` checks the stored owner. The `anvil` test deploys from a normal account.

Not in M6: constructor arguments.

## M7: internal calls

A contract function can call the contract's other functions, like `move(from, to, amount)` in the token. The reader inlines each call, so the IR, the lowering and the proof do not change, and the certificate checks the inlining.

### Done when

- [x] The callee's parameters become the argument expressions, and its other levels move above the caller's, so no variable is captured and Yul declares no local twice. A returned value replaces the bound variable; a tail action binds it.
- [x] `transfer` and `transferFrom` share `move`, and `mint` and `move` share `credit`. The token laws did not change.
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
