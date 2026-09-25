import { afterAll, beforeAll, expect, test } from 'bun:test';
import { bend, entries } from '../scripts/tools.js';
import { deploy, must } from './chain.js';

// Branches on a chain: each arm runs to the end of the call.
const program = 'tests/fixtures/branch/program.bend';
let chain;

beforeAll(async () => {
  chain = await deploy({ program, functions: entries.branch, args: [5n] });
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

test('arms that return Unit, in the runtime and in the deploy code', () => {
  expect(chain.word('marked()(uint256)')).toBe(5n);
  must(chain.send(chain.sender, 'mark(uint256)', '0'));
  expect(chain.word('marked()(uint256)')).toBe(5n);
  must(chain.send(chain.sender, 'mark(uint256)', '3'));
  expect(chain.word('marked()(uint256)')).toBe(3n);
  const code = '0x' + chain.bytecode + '0'.repeat(64);
  const receipt = JSON.parse(must(chain.cast('send', '--unlocked', '--from', chain.sender, '--json', '--create', code)));
  expect(BigInt(must(chain.cast('call', receipt.contractAddress, 'marked()(uint256)')))).toBe(0n);
});

test('a function writes when one of its arms writes', () => {
  const abi = JSON.parse(must(bend('src/abi.bend', program, ...entries.branch)));
  expect(abi.filter(f => f.type === 'function').map(f => [f.name, f.stateMutability])).toEqual([
    ['keep', 'nonpayable'], ['grade', 'view'], ['get', 'view'], ['mark', 'nonpayable'], ['marked', 'view']]);
}, 120_000);
