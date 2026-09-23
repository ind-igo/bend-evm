# bend-evm

- EVM backends for Bend, built on bend-frontend. They consume `Core.Program` only; never read upstream or the transport directly.
- Do not edit `vendor/bend-frontend` or the Bend it vendors. Change the frontend in its own repository, then bump the submodule deliberately.
- Use `cx overview` and `cx definition` to navigate code.
- Run `bun vendor/bend-frontend/vendor/bend/bend2/main.ts guide` before writing Bend. Keep statements in `LAWS.bend` and proofs in `PROOF.bend`.
- Before committing, run `bun run check` and `bun run test` (the Yul test requires solc and anvil).
- First-party implementation and proofs are Bend. Keep JavaScript limited to test harnesses.
- State the scope of every proof. Do not describe a backend as a verified compiler.
