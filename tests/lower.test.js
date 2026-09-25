import { expect, test } from 'bun:test';
import { copyFileSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

const root = path.resolve(import.meta.dir, '..');
const main = path.join(root, 'vendor/bend-frontend/vendor/bend/bend2/main.ts');

test('the preservation proof rejects a wrong lowering', () => {
  const dir = mkdtempSync(path.join(tmpdir(), 'bend-evm-lower-'));
  try {
    for (const file of ['Evm.bend', 'ir.bend', 'yul.bend', 'nat.bend', 'LAWS.bend', 'PROOF.bend']) {
      copyFileSync(path.join(root, 'src', file), path.join(dir, file));
    }
    const check = () => Bun.spawnSync([process.execPath, main, path.join(dir, 'PROOF.bend'), '--check-only']);
    // The copy must check before it is broken, or a missing file would pass the test.
    expect(check().stdout.toString()).toContain('All terms check.');
    const yul = readFileSync(path.join(dir, 'yul.bend'), 'utf8');
    for (const [from, to] of [
      ['Let{level, SLoad{loc}, lower(body, o)}', 'Let{level, Caller{}, lower(body, o)}'],
      ['      Lt{Atom{left}, Atom{right}}\n', '      Lt{Atom{right}, Atom{left}}\n'],
      ['      IsZero{lower.test(c)}', '      lower.test(c)'],
      ['def lower.cond(c: IR.Cond) -> Exp:\n  IsZero{lower.test(c)}', 'def lower.cond(c: IR.Cond) -> Exp:\n  lower.test(c)'],
      ['      Evm.time.of(Evm.world.of(s))', '      Evm.chain.of(Evm.world.of(s))'],
      ['Gt{Atom{right}, Sub{', 'Lt{Atom{right}, Sub{'],
      ['Nat.sub(Nat.sub(l, 1n), x)', 'Nat.sub(l, x)'],
      ['Check{Lt{Atom{left}, Atom{right}}, Let{', 'Check{Lt{Atom{right}, Atom{left}}, Let{'],
      ['Log{event, topics, data, lower(body, o)}', 'lower(body, o)'],
      ['Bool.pick(Nat, Nat.is_eq(c, 0n), n, y)', 'Bool.pick(Nat, Nat.is_eq(c, 0n), y, n)'],
      ['Not{Atom{IR.Lit{0n}}}', 'Atom{IR.Lit{0n}}'],
      ['If{lower.test(c), lower(yes, o), lower(no, o)}', 'If{lower.test(c), lower(no, o), lower(yes, o)}'],
      ['exec(no, o, env), exec(yes, o, env), R, k, s)', 'exec(yes, o, env), exec(no, o, env), R, k, s)'],
    ]) {
      expect(yul).toContain(from);
      writeFileSync(path.join(dir, 'yul.bend'), yul.replace(from, to));
      const checked = check();
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
  expect(init.stderr.toString()).toContain('init must return Unit');
  const poke = run('tests/fixtures/init.bend', 'poke');
  expect(poke.exitCode).not.toBe(0);
  expect(poke.stderr.toString()).toContain('a storage slot that is not a literal');
  const short = run('tests/fixtures/events.bend', 'short');
  expect(short.exitCode).not.toBe(0);
  expect(short.stderr.toString()).toContain('one word for each parameter');
}, 120_000);
