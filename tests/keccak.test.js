import { expect, test } from 'bun:test';
import path from 'node:path';

const root = path.resolve(import.meta.dir, '..');

test('selectors match cast sig, up to the one-block limit', () => {
  // 134 and 135 bytes put the 0x01 and 0x80 padding in the last byte.
  const signatures = ['get()', 'set(uint256)', 'transfer(address,uint256)',
    'f'.repeat(132) + '()', 'f'.repeat(133) + '()'];
  expect(signatures.at(-1).length).toBe(135);
  const ours = Bun.spawnSync([process.execPath, 'vendor/bend-frontend/host/run.js', 'src/selector.bend', ...signatures],
    { cwd: root, timeout: 120_000 });
  expect(ours.exitCode).toBe(0);
  const expected = signatures.map(s => Bun.spawnSync(['cast', 'sig', s]).stdout.toString().trim());
  expect(ours.stdout.toString().trim().split('\n')).toEqual(expected);
}, 120_000);
