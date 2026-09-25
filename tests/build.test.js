import { expect, test } from 'bun:test';
import { readFileSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { entries, sandbox, spawn } from '../scripts/tools.js';

test('build prints Yul only when the certificate and proof check', () => {
  sandbox(['src', 'scripts', 'examples/counter'], dir => {
    const build = () => spawn([process.execPath, 'scripts/build.js', 'examples/counter/program.bend', ...entries.counter],
      { cwd: dir });
    const good = build();
    expect(good.ok).toBe(true);
    expect(good.out).toContain('object "Contract"');
    // The law says increment adds 1, so PROOF.bend fails at it.
    const program = path.join(dir, 'examples/counter/program.bend');
    const text = readFileSync(program, 'utf8');
    expect(text).toContain('Evm.add(n, 1n)');
    writeFileSync(program, text.replace('Evm.add(n, 1n)', 'Evm.add(n, 2n)'));
    const bad = build();
    expect(bad.ok).toBe(false);
    expect(bad.out).toBe('');
    expect(bad.err).toContain('Location: LAWS.increment');
  });
}, 600_000);
