import { expect, test } from 'bun:test';
import { cpSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

const root = path.resolve(import.meta.dir, '..');

test('build prints Yul only when the certificate and proof check', () => {
  const dir = mkdtempSync(path.join(tmpdir(), 'bend-evm-build-'));
  try {
    for (const part of ['src', 'scripts', 'examples/counter']) {
      cpSync(path.join(root, part), path.join(dir, part), { recursive: true });
    }
    symlinkSync(path.join(root, 'vendor'), path.join(dir, 'vendor'));
    const build = () => Bun.spawnSync([process.execPath, 'scripts/build.js', 'examples/counter/program.bend',
      'get', 'increment', 'decrement', 'set'], { cwd: dir, timeout: 300_000 });
    const good = build();
    expect(good.exitCode).toBe(0);
    expect(good.stdout.toString()).toContain('object "Contract"');
    // The law says increment adds 1.
    const program = path.join(dir, 'examples/counter/program.bend');
    const text = readFileSync(program, 'utf8');
    expect(text).toContain('Evm.add(n, 1n)');
    writeFileSync(program, text.replace('Evm.add(n, 1n)', 'Evm.add(n, 2n)'));
    const bad = build();
    expect(bad.exitCode).not.toBe(0);
    expect(bad.stdout.toString()).toBe('');
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}, 300_000);
