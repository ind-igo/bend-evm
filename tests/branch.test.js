import { afterAll, beforeAll, expect, test } from 'bun:test';
import { deploy, must } from './chain.js';

// Branches on a chain: each arm runs to the end of the call.
let chain;

beforeAll(async () => {
  chain = await deploy('tests/fixtures/branch/program.bend', ['keep', 'grade', 'get']);
}, 120_000);

afterAll(() => chain?.stop());

test('keep stores only a nonzero word', () => {
  const keep = x => chain.word('keep(uint256)(uint256)', String(x));
  expect(keep(0)).toBe(0n);
  expect(keep(5)).toBe(1n);
  must(chain.send(chain.sender, 'keep(uint256)', '7'));
  expect(chain.word('get()(uint256)')).toBe(7n);
  must(chain.send(chain.sender, 'keep(uint256)', '0'));
  expect(chain.word('get()(uint256)')).toBe(7n);
});

test('grade takes the arm of each nested branch', () => {
  const grade = x => chain.word('grade(uint256)(uint256)', String(x));
  expect([0, 9, 10, 99, 100, 250].map(grade)).toEqual([0n, 0n, 1n, 1n, 0n, 150n]);
});
