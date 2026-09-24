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

Mappings (keccak slots), `address` arguments, events, and wider literals.
