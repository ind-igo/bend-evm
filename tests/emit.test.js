import { expect, test } from 'bun:test';
import { cpSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { run } from './chain.js';

// Events: Evm.emit(Event(...)) with a def whose result type is Evm.Event.
const root = path.resolve(import.meta.dir, '..');
const host = 'vendor/bend-frontend/host/run.js';

test('compile rejects events that the ABI cannot encode', () => {
  for (const [name, error] of [['late', 'Indexed event fields must come before the others'],
    ['wide', 'at most three indexed words'], ['raw', 'whose result type is Evm.Event'],
    ['plain', 'whose result type is Evm.Event']]) {
    const result = run(process.execPath, host, 'src/compile.bend', 'tests/fixtures/emit/bad.bend', name);
    expect(result.ok).toBe(false);
    expect(result.err).toContain(error);
  }
}, 120_000);

test('the ABI rejects one signature with different indexed parameters', () => {
  const result = run(process.execPath, host, 'src/abi.bend', 'tests/fixtures/emit/bad.bend', 'one', 'two');
  expect(result.ok).toBe(false);
  expect(result.err).toContain('Two events have the signature Moved(address,uint256) but different indexed parameters');
}, 120_000);

test('an event whose body disagrees with its parameters fails the certificate', () => {
  const dir = mkdtempSync(path.join(tmpdir(), 'bend-evm-emit-'));
  try {
    for (const file of ['src/Evm.bend', 'src/ir.bend', 'tests/fixtures/emit']) {
      cpSync(path.join(root, file), path.join(dir, file), { recursive: true });
    }
    const program = path.join(dir, 'tests/fixtures/emit/program.bend');
    const good = readFileSync(program, 'utf8');
    for (const [from, to] of [['[from], [amount]', '[amount], [from]'], ['Moved(address,uint256)', 'Moved(uint256,uint256)']]) {
      expect(good).toContain(from);
      writeFileSync(program, good.replace(from, to));
      const checked = run(process.execPath, 'vendor/bend-frontend/vendor/bend/bend2/main.ts',
        path.join(dir, 'tests/fixtures/emit/CERT.bend'), '--check-only');
      expect(checked.ok).toBe(false);
      expect(checked.out + checked.err).toContain('Location: moved');
    }
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}, 120_000);
