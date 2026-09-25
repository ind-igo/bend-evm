import { expect, test } from 'bun:test';
import { readFileSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { bend, check, sandbox } from '../scripts/tools.js';

// Events: Evm.emit(Event(...)) with a def whose result type is Evm.Event.
// tests/reject.test.js has the events that compile rejects.

test('the ABI rejects one signature with different indexed parameters', () => {
  const result = bend('src/abi.bend', 'tests/fixtures/emit/bad.bend', 'one', 'two');
  expect(result.ok).toBe(false);
  expect(result.err).toContain('Two events have the signature Moved(address,uint256) but different indexed parameters');
}, 120_000);

test('an event whose body disagrees with its parameters fails the certificate', () => {
  sandbox(['src/Evm.bend', 'src/ir.bend', 'tests/fixtures/emit'], dir => {
    const program = path.join(dir, 'tests/fixtures/emit/program.bend');
    const good = readFileSync(program, 'utf8');
    for (const [from, to] of [['[from], [amount]', '[amount], [from]'], ['Moved(address,uint256)', 'Moved(uint256,uint256)']]) {
      expect(good).toContain(from);
      writeFileSync(program, good.replace(from, to));
      const checked = check(path.join(dir, 'tests/fixtures/emit/CERT.bend'));
      expect(checked.ok).toBe(false);
      expect(checked.out + checked.err).toContain('Location: moved');
    }
  });
}, 120_000);
