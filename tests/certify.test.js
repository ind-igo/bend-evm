import { expect, test } from 'bun:test';
import { readFileSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { bend, check, entries, root, sandbox } from '../scripts/tools.js';

// The token's certificate is checked where it is built, in token.test.js.
for (const [program, functions] of [
  ['examples/counter', entries.counter],
  ['tests/fixtures/branch', entries.branch],
  ['tests/fixtures/emit', entries.emit],
]) {
  test(`the committed ${program} certificate is current`, () => {
    const generated = bend('src/certify.bend', `${program}/program.bend`, ...functions);
    expect(generated.ok).toBe(true);
    expect(generated.text).toBe(readFileSync(path.join(root, `${program}/CERT.bend`), 'utf8'));
  }, 120_000);
}

// Each mutation of a copied certificate must fail at its law.
function mutated(program, mutations) {
  sandbox(['src/Evm.bend', 'src/ir.bend', `${program}/program.bend`, `${program}/CERT.bend`], dir => {
    const cert = path.join(dir, `${program}/CERT.bend`);
    const good = readFileSync(cert, 'utf8');
    for (const [from, to, law] of mutations) {
      expect(good).toContain(from);
      writeFileSync(cert, good.replace(from, to));
      const checked = check(cert);
      expect(checked.ok).toBe(false);
      expect(checked.out + checked.err).toContain(`Location: ${law}`);
    }
  });
}

test('a certificate for the wrong IR does not check', () => {
  mutated('examples/counter', [
    ['IR.Lit{7n}', 'IR.Lit{8n}', 'set'],
    ['IR.SStore{IR.Plain{IR.Lit{0n}}, IR.Var{1n}}', 'IR.SStore{IR.Plain{IR.Lit{0n}}, IR.Var{0n}}', 'increment'],
    ['IR.Tail{IR.SLoad{IR.Plain{IR.Lit{0n}}}}', 'IR.Tail{IR.SLoad{IR.Plain{IR.Lit{1n}}}}', 'get'],
    ['IR.Tail{IR.SLoad{IR.Plain{IR.Lit{0n}}}}', 'IR.Tail{IR.SLoad{IR.Mapped{IR.Plain{IR.Lit{0n}}, IR.Lit{0n}}}}', 'get'],
    // An unbound Var reads as 0, like the source's literal key, so only the scope check catches it.
    ['IR.Tail{IR.SLoad{IR.Plain{IR.Lit{0n}}}}', 'IR.Tail{IR.SLoad{IR.Plain{IR.Var{5n}}}}', 'get'],
  ]);
}, 120_000);

test('a certificate for the wrong branch does not check', () => {
  mutated('tests/fixtures/branch', [
    ['IR.If{IR.Eq{IR.Var{0n}, IR.Lit{0n}},\n    IR.Return{IR.Lit{0n}},',
      'IR.If{IR.Eq{IR.Var{0n}, IR.Lit{1n}},\n    IR.Return{IR.Lit{0n}},', 'keep'],
    ['IR.If{IR.Eq{IR.Var{0n}, IR.Lit{0n}},\n    IR.Return{IR.Lit{0n}},',
      'IR.If{IR.Eq{IR.Var{0n}, IR.Lit{0n}},\n    IR.Return{IR.Lit{1n}},', 'keep'],
    ['IR.If{IR.Lt{IR.Var{0n}, IR.Lit{100n}},', 'IR.If{IR.Lt{IR.Var{0n}, IR.Lit{99n}},', 'grade'],
  ]);
}, 120_000);

// A copied Evm.bend and ir.bend could define different semantics.
test('certify refuses a contract that imports another Evm.bend', () => {
  sandbox(['src/Evm.bend', 'src/ir.bend', 'examples/counter/program.bend'], dir => {
    const copy = bend('src/certify.bend', path.join(dir, 'examples/counter/program.bend'), 'get');
    expect(copy.ok).toBe(false);
    expect(copy.err).toContain("must import this backend's Evm.bend");
  });
}, 120_000);
