import { afterAll, beforeAll, expect, test } from 'bun:test';
import { bend } from '../scripts/tools.js';
import { deploy, must, reverts, run } from './chain.js';

// Constant strings, uint8 and bool on a chain, and the ABI JSON.
const program = 'tests/fixtures/meta.bend';
const functions = ['name', 'symbol', 'decimals', 'echo'];
let chain;

beforeAll(async () => {
  chain = await deploy({ program, functions });
}, 120_000);

afterAll(() => chain?.stop());

const call = (...args) => chain.cast('call', chain.address, ...args);

test('constant strings and a uint8 decode through the ABI', () => {
  expect(must(call('name()(string)'))).toBe('"Bend Token"');
  expect(must(call('symbol()(string)'))).toBe('"A symbol that is longer than one word of thirty-two bytes"');
  expect(must(call('decimals()(uint8)'))).toBe('18');
});

test('uint8 and bool arguments must be in range', () => {
  expect(must(call('echo(uint8,bool)(uint256)', '255', 'true'))).toBe('256');
  const selector = must(run('cast', 'sig', 'echo(uint8,bool)'));
  const hex = x => x.toString(16).padStart(64, '0');
  const raw = (x, flag) => chain.cast('call', chain.address, selector + hex(x) + hex(flag));
  expect(raw(255, 1).ok).toBe(true);
  reverts(raw(256, 1));
  reverts(raw(1, 2));
});

test('the ABI JSON describes the functions', () => {
  const abi = JSON.parse(must(bend('src/abi.bend', program, ...functions)));
  expect(abi.map(f => [f.name, f.outputs.map(o => o.type), f.stateMutability])).toEqual([
    ['name', ['string'], 'pure'], ['symbol', ['string'], 'pure'], ['decimals', ['uint8'], 'view'],
    ['echo', ['uint256'], 'view']]);
  expect(abi[3].inputs).toEqual([{ name: 'x', type: 'uint8' }, { name: 'flag', type: 'bool' }]);
}, 120_000);
