# bend-evm

An EVM backend for **Bend 2**, written in Bend. It consumes the checked `Core.Program` from [bend-frontend](https://github.com/ind-igo/bend-frontend).

Contracts are ordinary Bend functions in the `Contract` monad of [Evm.bend](src/Evm.bend). Specifications are laws about them, as in [examples/counter/LAWS.bend](examples/counter/LAWS.bend).

```text
contract.bend ─ Frontend.check ─ read ─→ IR ─ lower ─→ Yul ─ solc ─→ bytecode
                                          │           │
                  certificate: IR ≡ contract    law: lower preserves every IR command
```

[ROADMAP.md](ROADMAP.md) gives the current goal: the Counter on a chain, with every step proved or tested.

## Use

Requires Git and Bun. The tests also need `solc`, `anvil` and `cast`.

```sh
git submodule update --init --recursive
bun run check   # check every Bend entry point and proof
bun run test
bun vendor/bend-frontend/host/run.js src/certify.bend examples/counter/program.bend get increment set \
  > examples/counter/CERT.bend
mkdir -p build
bun vendor/bend-frontend/host/run.js src/compile.bend examples/counter/program.bend get increment set \
  > build/Counter.yul
solc --strict-assembly --evm-version shanghai --bin build/Counter.yul
```

[tests/counter.test.js](tests/counter.test.js) deploys the Counter on `anvil` and calls it through the standard ABI.

The frontend is a submodule at `vendor/bend-frontend`, and it pins Bend at `vendor/bend-frontend/vendor/bend`. Its `host/run.js` launches the Bend drivers here with the checker attached, and keeps compiled tools in `vendor/bend-frontend/build/cache`. See [Connecting Bend to backends](https://github.com/ind-igo/bend-frontend/blob/main/docs/backends.md) for how a backend uses the frontend, and the frontend's README for what it trusts.

## Certificates

[certify.bend](src/certify.bend) prints each entry as a literal [IR](src/ir.bend) value and a law stating that `IR.call` of that value equals the source function. `IR.call` reverts when a variable is not bound, then runs the IR. The IR constructors map one to one to DSL calls, so both sides normalize to the same term and `{==}` proves the law.

The reader ([read.bend](src/read.bend)) is not trusted: a wrong IR makes the certificate fail. The trusted base is the Bend checker, the semantics in `Evm.bend` and `ir.bend`, and the shape of the law that certify.bend prints. certify.bend rejects a contract that imports a different `Evm.bend`, and a parameter list that does not bind levels 0, 1, ... in order.

## Lowering

[yul.bend](src/yul.bend) defines the Yul fragment that the IR needs, its meaning over the same `State`, and `lower`. [LAWS.bend](src/LAWS.bend) states that running `lower(cmd)` gives the same outcome as `IR.run(cmd)` for every command, output kind, environment and state, and [PROOF.bend](src/PROOF.bend) proves it by induction. [compile.bend](src/compile.bend) prints the Yul with an ABI dispatcher, and [keccak.bend](src/keccak.bend) computes the selectors.

Checked add lowers to `if gt(b, sub(not(0), a)) { revert(0, 0) }` and a wrapping `add`. The model's `add`, `sub`, `not` and `gt` are the EVM's operations on words below `limit`. Above `limit` the EVM has no words, so the model picks results that make the check revert. The proof therefore needs no invariant that words stay below `limit`, only the lemma that the check is zero exactly when `a + b < limit`.

Proved: contract ≡ IR (certificate) and IR ≡ Yul model (the law). Tested, not proved: the printer, the dispatcher and ABI decoding, `solc`, and the match between the Yul model and the EVM on words below 2^256.

## Model

- Words are `Nat`. Checked `add` reverts at the state's `limit`, which is 2^256 on the EVM. Proofs keep the limit symbolic: the checker writes any closed Nat near 2^256 out in unary.
- Storage is an association list: the newest slot wins and missing slots read as zero. A revert discards all state.
- Supported now: `sload`, `sstore`, `caller`, checked `add`, `require`, `pure`, Nat parameters and literal constants. The reader rejects everything else.

## Limits

- The certificate's imports are relative. Save it as `CERT.bend` beside the contract, or it names other files.
- certify.bend must run through the frontend's `host/run.js`, which gives it its own path in `BEND_ENTRY`.
- Literals are limited by `Nat.read` (about 2^48). Source Nat literals already stop at 2^32 - 1.
- Parameters and results are `uint256`.
- In the reader, match on `Call` names, not on nested `Term` patterns: nested patterns over Term made checking take 6 GB.
