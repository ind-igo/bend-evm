import { expect, test } from 'bun:test';
import { readFileSync, writeFileSync, mkdtempSync, rmSync, copyFileSync, mkdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

const root = path.resolve(import.meta.dir, '..');
const run = 'vendor/bend-frontend/host/run.js';
const main = 'vendor/bend-frontend/vendor/bend/bend2/main.ts';
const bend = (...args) => Bun.spawnSync([process.execPath, ...args], { cwd: root, timeout: 120_000 });

for (const [program, functions] of [
  ['examples/counter', ['get', 'increment', 'decrement', 'set']],
  ['tests/fixtures/branch', ['init', 'keep', 'grade', 'get', 'mark', 'marked']],
  ['tests/fixtures/emit', ['moved']],
  ['examples/token', ['name', 'symbol', 'decimals', 'init', 'owner', 'transferOwnership', 'totalSupply', 'balanceOf', 'transfer', 'mint', 'burn', 'allowance', 'approve',
    'transferFrom', 'nonces', 'DOMAIN_SEPARATOR', 'permit']],
]) {
  test(`the committed ${program} certificate is current`, () => {
    const generated = bend(run, 'src/certify.bend', `${program}/program.bend`, ...functions);
    expect(generated.exitCode).toBe(0);
    expect(generated.stdout.toString()).toBe(readFileSync(path.join(root, `${program}/CERT.bend`), 'utf8'));
  }, 120_000);
}

// Copies the backend and a program to a temporary directory, then checks
// that each mutation of the certificate fails at its law.
function mutated(program, mutations, more = () => {}) {
  const dir = mkdtempSync(path.join(tmpdir(), 'bend-evm-cert-'));
  try {
    mkdirSync(path.join(dir, 'src'));
    mkdirSync(path.join(dir, program), { recursive: true });
    for (const file of ['src/Evm.bend', 'src/ir.bend', `${program}/program.bend`, `${program}/CERT.bend`]) {
      copyFileSync(path.join(root, file), path.join(dir, file));
    }
    const cert = path.join(dir, `${program}/CERT.bend`);
    const good = readFileSync(cert, 'utf8');
    for (const [from, to, law] of mutations) {
      expect(good).toContain(from);
      writeFileSync(cert, good.replace(from, to));
      const checked = bend(main, cert, '--check-only');
      expect(checked.exitCode).not.toBe(0);
      expect(checked.stdout.toString() + checked.stderr.toString()).toContain(`Location: ${law}`);
    }
    more(dir);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test('a certificate for the wrong IR does not check', () => {
  mutated('examples/counter', [
    ['IR.Lit{7n}', 'IR.Lit{8n}', 'set'],
    ['IR.SStore{IR.Plain{IR.Lit{0n}}, IR.Var{1n}}', 'IR.SStore{IR.Plain{IR.Lit{0n}}, IR.Var{0n}}', 'increment'],
    ['IR.Tail{IR.SLoad{IR.Plain{IR.Lit{0n}}}}', 'IR.Tail{IR.SLoad{IR.Plain{IR.Lit{1n}}}}', 'get'],
    ['IR.Tail{IR.SLoad{IR.Plain{IR.Lit{0n}}}}', 'IR.Tail{IR.SLoad{IR.Mapped{IR.Plain{IR.Lit{0n}}, IR.Lit{0n}}}}', 'get'],
    // An unbound Var reads as 0, like the source's literal key, so only the scope check catches it.
    ['IR.Tail{IR.SLoad{IR.Plain{IR.Lit{0n}}}}', 'IR.Tail{IR.SLoad{IR.Plain{IR.Var{5n}}}}', 'get'],
  ], dir => {
    // The copied Evm.bend and ir.bend could define different semantics.
    const copy = bend(run, 'src/certify.bend', path.join(dir, 'examples/counter/program.bend'), 'get');
    expect(copy.exitCode).not.toBe(0);
    expect(copy.stderr.toString()).toContain("must import this backend's Evm.bend");
  });
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
