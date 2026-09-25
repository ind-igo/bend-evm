import { afterAll, beforeAll, expect, test } from 'bun:test';
import { deploy, must, run } from './chain.js';

// Branches on a chain: each arm runs to the end of the call.
const functions = ['init', 'keep', 'grade', 'get', 'mark', 'marked'];
const host = 'vendor/bend-frontend/host/run.js';
let chain;

beforeAll(async () => {
  chain = await deploy('tests/fixtures/branch/program.bend', functions, { args: [5n] });
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
  const abi = JSON.parse(must(run(process.execPath, host, 'src/abi.bend', 'tests/fixtures/branch/program.bend',
    ...functions)));
  expect(abi.filter(f => f.type === 'function').map(f => [f.name, f.stateMutability])).toEqual([
    ['keep', 'nonpayable'], ['grade', 'view'], ['get', 'view'], ['mark', 'nonpayable'], ['marked', 'view']]);
}, 120_000);

test('compile rejects a branch that is not the last step', () => {
  for (const [name, error] of [['early', 'A branch must be the last step'],
    ['middle', 'A call to a function that branches must be the last step']]) {
    const result = run(process.execPath, host, 'src/compile.bend', 'tests/fixtures/branch/bad.bend', name);
    expect(result.ok).toBe(false);
    expect(result.err).toContain(error);
  }
}, 120_000);
