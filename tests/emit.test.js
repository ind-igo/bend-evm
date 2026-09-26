import { expect, test } from 'bun:test';
import { readFileSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { bend, check, entries, must, sandbox } from '../scripts/tools.js';

// Events and errors: Evm.emit(Event(...)) with a def whose result type is
// Evm.Event, and Evm.ensure(ok, Error(...)) with one whose result type is
// Evm.Error. tests/reject.test.js has the ones that compile rejects.

test('the ABI rejects one signature with different indexed parameters', () => {
  const result = bend('src/abi.bend', 'tests/fixtures/emit/bad.bend', 'one', 'two');
  expect(result.ok).toBe(false);
  expect(result.err).toContain('Two events have the signature Moved(address,uint256) but different indexed parameters');
}, 120_000);

test('the ABI lists the events and errors with their parameter names', () => {
  const abi = JSON.parse(must(bend('src/abi.bend', 'tests/fixtures/emit/program.bend', ...entries.emit)));
  expect(abi.filter(item => item.type === 'event' || item.type === 'error')).toEqual([
    { type: 'event', name: 'Moved', anonymous: false, inputs: [
      { name: 'from', type: 'address', indexed: true }, { name: 'amount', type: 'uint256', indexed: false }] },
    { type: 'error', name: 'TooSmall', inputs: [{ name: 'amount', type: 'uint256' }, { name: 'least', type: 'uint256' }] },
  ]);
}, 120_000);

test('the ABI gives no names when two defs with one signature disagree on them', () => {
  const abi = JSON.parse(must(bend('src/abi.bend', 'tests/fixtures/emit/names.bend', 'check')));
  expect(abi.find(item => item.type === 'error').inputs).toEqual([{ name: '', type: 'uint256' }, { name: '', type: 'uint256' }]);
}, 120_000);

test('an event or error whose body disagrees with its def fails the certificate', () => {
  sandbox(['src/Evm.bend', 'src/ir.bend', 'tests/fixtures/emit'], dir => {
    const program = path.join(dir, 'tests/fixtures/emit/program.bend');
    const good = readFileSync(program, 'utf8');
    for (const [from, to] of [['[from], [amount]', '[amount], [from]'], ['"Moved"', '"Move"'],
      ['[amount, least]', '[least, amount]'], ['"TooSmall"', '"TooLow"']]) {
      expect(good).toContain(from);
      writeFileSync(program, good.replace(from, to));
      const checked = check(path.join(dir, 'tests/fixtures/emit/CERT.bend'));
      expect(checked.ok).toBe(false);
      expect(checked.out + checked.err).toMatch(/Location: (moved|take)/);
    }
  });
}, 120_000);
