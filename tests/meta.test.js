import { afterAll, beforeAll, expect, test } from 'bun:test';
import { deploy, must, run } from './chain.js';

// Constant strings, uint8 and bool on a chain, and the ABI JSON.
let chain;

beforeAll(async () => {
  chain = await deploy('tests/fixtures/meta.bend', ['name', 'symbol', 'decimals', 'echo']);
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
  const word = x => x.toString(16).padStart(64, '0');
  const raw = (x, flag) => chain.cast('call', chain.address, selector + word(x) + word(flag));
  expect(raw(255, 1).ok).toBe(true);
  expect(raw(256, 1).ok).toBe(false);
  expect(raw(1, 2).ok).toBe(false);
});

test('the ABI JSON describes the functions', () => {
  const abi = JSON.parse(must(run(process.execPath, 'vendor/bend-frontend/host/run.js', 'src/abi.bend',
    'tests/fixtures/meta.bend', 'name', 'symbol', 'decimals', 'echo')));
  expect(abi.map(f => [f.name, f.outputs.map(o => o.type), f.stateMutability])).toEqual([
    ['name', ['string'], 'pure'], ['symbol', ['string'], 'pure'], ['decimals', ['uint8'], 'view'],
    ['echo', ['uint256'], 'view']]);
  expect(abi[3].inputs).toEqual([{ name: 'x', type: 'uint8' }, { name: 'flag', type: 'bool' }]);
}, 120_000);

test('a constant with a signature over 135 bytes does not compile', () => {
  const result = run(process.execPath, 'vendor/bend-frontend/host/run.js', 'src/compile.bend',
    'tests/fixtures/meta.bend', 'decimals', 'a'.repeat(134));
  expect(result.ok).toBe(false);
  expect(result.err).toContain('signatures over 135 bytes are not supported');
}, 120_000);
