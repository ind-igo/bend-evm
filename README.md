# bend-evm

An EVM backend for **Bend 2**, written in Bend. It consumes the checked `Core.Program` from [bend-frontend](https://github.com/ind-igo/bend-frontend).

Contracts are ordinary Bend functions in the `Contract` monad of [Evm.bend](src/Evm.bend). Specifications are laws about them, as in [examples/counter/LAWS.bend](examples/counter/LAWS.bend) and [examples/token/LAWS.bend](examples/token/LAWS.bend).

```text
contract.bend ─ Frontend.check ─ read ─→ IR ─ lower ─→ Yul ─ solc ─→ bytecode
                                          │           │
                  certificate: IR ≡ contract    law: lower preserves every IR command
```

[ROADMAP.md](ROADMAP.md) gives the milestones: the Counter on a chain (M1), a minimal token (M2), laws for any state (M3), the rest of ERC-20 (M4) and select (M5), all done.

## Use

Requires Git and Bun. The tests also need `solc`, `anvil` and `cast`.

```sh
git submodule update --init --recursive
bun run check   # check every Bend entry point and proof
bun run test
bun vendor/bend-frontend/host/run.js src/certify.bend examples/counter/program.bend get increment decrement set \
  > examples/counter/CERT.bend
mkdir -p build
bun vendor/bend-frontend/host/run.js src/compile.bend examples/counter/program.bend get increment decrement set \
  > build/Counter.yul
solc --strict-assembly --evm-version shanghai --bin build/Counter.yul
```

[tests/counter.test.js](tests/counter.test.js) and [tests/token.test.js](tests/token.test.js) deploy the examples on `anvil` and call them through the standard ABI. The token's functions are `totalSupply balanceOf transfer mint allowance approve transferFrom`.

The frontend is a submodule at `vendor/bend-frontend`, and it pins Bend at `vendor/bend-frontend/vendor/bend`. Its `host/run.js` launches the Bend drivers here with the checker attached, and keeps compiled tools in `vendor/bend-frontend/build/cache`. See [Connecting Bend to backends](https://github.com/ind-igo/bend-frontend/blob/main/docs/backends.md) for how a backend uses the frontend, and the frontend's README for what it trusts.

## Certificates

[certify.bend](src/certify.bend) prints each entry as a literal [IR](src/ir.bend) value and a law stating that `IR.call` of that value equals the source function. `IR.call` reverts when a variable is not bound, then runs the IR. The IR constructors map one to one to DSL calls, so both sides normalize to the same term and `{==}` proves the law.

The reader ([read.bend](src/read.bend)) is not trusted: a wrong IR makes the certificate fail. The trusted base is the Bend checker, the semantics in `Evm.bend` and `ir.bend`, and the shape of the law that certify.bend prints. certify.bend rejects a contract that imports a different `Evm.bend`, and a parameter list that does not bind levels 0, 1, ... in order.

## Lowering

[yul.bend](src/yul.bend) defines the Yul fragment that the IR needs, its meaning over the same `State`, and `lower`. [LAWS.bend](src/LAWS.bend) states that running `lower(cmd)` gives the same outcome as `IR.run(cmd)` for every command, output kind, environment, continuation and state, and [PROOF.bend](src/PROOF.bend) proves it by induction. [compile.bend](src/compile.bend) prints the Yul with an ABI dispatcher, and [keccak.bend](src/keccak.bend) computes the selectors and event topics.

Checked add lowers to `if gt(b, sub(not(0), a)) { revert(0, 0) }` and a wrapping `add`. Checked sub lowers to `if lt(a, b) { revert(0, 0) }` and `sub(a, b)`. `select` lowers to a runtime Yul function `select(c, a, b)`, and `max()` to `not(0)`. The model's `add`, `sub`, `not` and `gt` are the EVM's operations on words below `limit`. Above `limit` the EVM has no words, so the model picks results that keep the proof exact: the add check reverts, and `sub(a, b)` is `a - b` whenever `a ≥ b`. The proof therefore needs no invariant that words stay below `limit`, only the lemma that the check is zero exactly when `a + b < limit`.

Proved: contract ≡ IR (certificate) and IR ≡ Yul model (the law). Tested, not proved: the printer, the dispatcher and ABI decoding, the mapping layout, event topics, `solc`, and the match between the Yul model and the EVM on words below 2^256.

## Model

- A contract passes its result and state to a continuation, and `Evm.run(A, m, s)` gives its outcome. Each check is then a `Bool.pick` at the top of the normal form. So a law can state every outcome from any state, with symbolic storage, caller, addresses and amounts, and `{==}` proves it. See the [counter](examples/counter/LAWS.bend) and [token](examples/token/LAWS.bend) laws.
- Words are `Nat`. Checked `add` reverts at the state's `limit`, which is 2^256 on the EVM, and checked `sub` reverts below zero. Proofs keep the limit symbolic: the checker writes any closed Nat near 2^256 out in unary.
- Storage is an association list: the newest slot wins and missing slots read as zero. A key is a plain slot or an entry of a mapping, `Mapped{base, key}`, where `base` is a key too. The printer puts an entry at `keccak256(key . base)`, as Solidity does, so the model assumes that Keccak has no collisions. A revert discards all state.
- Events are `log(signature, topics, data)`: an ABI signature, at most three indexed words and one data word. The state keeps them newest first, so a revert drops them too. Topic 0 is the signature's Keccak-256, which the printer computes.
- Supported now: `sload`, `sstore`, mappings (`load(slot, key)`, `store(slot, key, value)`) and nested mappings (`load2(slot, outer, inner)`, `store2(slot, outer, inner, value)`), `caller`, checked `add` and `sub`, `select(cond, a, b)`, `max()`, `require`, `log`, `pure`, Nat and address parameters, and literal constants. The reader rejects everything else.

## Limits

- The certificate's imports are relative. Save it as `CERT.bend` beside the contract, or it names other files.
- certify.bend must run through the frontend's `host/run.js`, which gives it its own path in `BEND_ENTRY`.
- Literals are limited by `Nat.read` (about 2^48). Source Nat literals already stop at 2^32 - 1.
- Parameters are `uint256` (`Nat`) or `address` (`Evm.Address`, which is `Nat`); the dispatcher reverts on an address above 2^160. Results are `uint256`; a `bool` result is the word 1 or 0, which has the same encoding.
- There is no `if`/`else` over contracts, only `require` and `select` over words. See ROADMAP.md (M5) for why.
- In the reader, match on `Call` names, not on nested `Term` patterns: nested patterns over Term made checking take 6 GB.
