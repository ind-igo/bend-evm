import { expect, test } from 'bun:test';
import { copyFileSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

const root = path.resolve(import.meta.dir, '..');
const main = path.join(root, 'vendor/bend-frontend/vendor/bend/bend2/main.ts');

test('the preservation proof rejects a wrong lowering', () => {
  const dir = mkdtempSync(path.join(tmpdir(), 'bend-evm-lower-'));
  try {
    for (const file of ['Evm.bend', 'ir.bend', 'yul.bend', 'LAWS.bend', 'PROOF.bend']) {
      copyFileSync(path.join(root, 'src', file), path.join(dir, file));
    }
    const yul = readFileSync(path.join(dir, 'yul.bend'), 'utf8');
    for (const [from, to] of [
      ['Let{level, SLoad{loc}, lower(body, o)}', 'Let{level, Caller{}, lower(body, o)}'],
      ['IsZero{Lt{Atom{left}, Atom{right}}}', 'IsZero{Lt{Atom{right}, Atom{left}}}'],
      ['Gt{Atom{right}, Sub{', 'Lt{Atom{right}, Sub{'],
      ['Nat.sub(Nat.sub(l, 1n), x)', 'Nat.sub(l, x)'],
      ['Check{Lt{Atom{left}, Atom{right}}, Let{', 'Check{Lt{Atom{right}, Atom{left}}, Let{'],
      ['Log{event, topics, data, lower(body, o)}', 'lower(body, o)'],
      ['Bool.pick(Nat, Nat.is_eq(c, 0n), n, y)', 'Bool.pick(Nat, Nat.is_eq(c, 0n), y, n)'],
      ['Not{Atom{IR.Lit{0n}}}', 'Atom{IR.Lit{0n}}'],
    ]) {
      expect(yul).toContain(from);
      writeFileSync(path.join(dir, 'yul.bend'), yul.replace(from, to));
      const checked = Bun.spawnSync([process.execPath, main, path.join(dir, 'PROOF.bend'), '--check-only']);
      expect(checked.exitCode).not.toBe(0);
      expect(checked.stdout.toString() + checked.stderr.toString()).toContain('Location:');
    }
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}, 120_000);

test('compile rejects functions outside the contract DSL', () => {
  const run = (file, name) => Bun.spawnSync([process.execPath, 'vendor/bend-frontend/host/run.js', 'src/compile.bend',
    file, name], { cwd: root, timeout: 120_000 });
  const plain = run('vendor/bend-frontend/tests/fixtures/program.bend', 'sum');
  expect(plain.exitCode).not.toBe(0);
  expect(plain.stderr.toString()).toContain('Expected an Evm.Contract result');
  const unknown = run('examples/counter/program.bend', 'missing');
  expect(unknown.exitCode).not.toBe(0);
  expect(unknown.stderr.toString()).toContain('Unknown contract function');
  const quoted = run('tests/fixtures/events.bend', 'quoted');
  expect(quoted.exitCode).not.toBe(0);
  expect(quoted.stderr.toString()).toContain('Event signatures must be ABI signatures');
  const wide = run('tests/fixtures/events.bend', 'wide');
  expect(wide.exitCode).not.toBe(0);
  expect(wide.stderr.toString()).toContain('at most three indexed words');
  const init = run('tests/fixtures/init.bend', 'init');
  expect(init.exitCode).not.toBe(0);
  expect(init.stderr.toString()).toContain('init takes no parameters');
}, 120_000);
