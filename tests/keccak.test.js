import { expect, test } from 'bun:test';
import { bend, must, run } from '../scripts/tools.js';

test('selectors and hashes match cast, up to the one-block limit', () => {
  // 134 and 135 bytes put the 0x01 and 0x80 padding in the last byte.
  const signatures = ['get()', 'set(uint256)', 'transfer(address,uint256)',
    'f'.repeat(132) + '()', 'f'.repeat(133) + '()'];
  expect(signatures.at(-1).length).toBe(135);
  const ours = must(bend('src/selector.bend', ...signatures));
  const cast = (...args) => must(run('cast', ...args));
  expect(ours.split('\n')).toEqual(signatures.map(s => `${cast('sig', s)} ${cast('keccak', s)}`));
}, 120_000);
