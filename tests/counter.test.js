import { afterAll, beforeAll, expect, test } from 'bun:test';
import { entries } from '../scripts/tools.js';
import { deploy, must, reverts } from './chain.js';

// The owner that examples/counter/program.bend names.
const owner = '0x0000000000000000000000000000000000000007';
const max = '0x' + 'f'.repeat(64);
let chain, sender, send, get;

beforeAll(async () => {
  chain = await deploy({ program: 'examples/counter/program.bend', functions: entries.counter });
  chain.fund(owner);
  ({ sender, send } = chain);
  get = () => chain.word('get()(uint256)');
}, 120_000);

afterAll(() => chain?.stop());

test('get and increment', () => {
  expect(get()).toBe(0n);
  must(send(sender, 'increment()'));
  must(send(sender, 'increment()'));
  expect(get()).toBe(2n);
});

test('only the owner can set', () => {
  must(send(owner, 'set(uint256)', '42'));
  expect(get()).toBe(42n);
  reverts(send(sender, 'set(uint256)', '7'));
  expect(get()).toBe(42n);
});

test('increment reverts on overflow', () => {
  must(chain.cast('rpc', 'anvil_setStorageAt', chain.address, '0x0', max));
  reverts(send(sender, 'increment()'));
  expect(get()).toBe(2n ** 256n - 1n);
  must(send(owner, 'set(uint256)', '0'));
});

test('decrement reverts at zero', () => {
  must(send(sender, 'increment()'));
  must(send(sender, 'decrement()'));
  expect(get()).toBe(0n);
  reverts(send(sender, 'decrement()'));
  expect(get()).toBe(0n);
});

test('rejects ETH, unknown selectors and short calldata', () => {
  reverts(send(sender, 'increment()', '--value', '1'));
  reverts(chain.cast('call', chain.address, 'missing()'));
  reverts(chain.cast('call', '--from', owner, chain.address, '0x60fe47b1'));
  expect(get()).toBe(0n);
});
