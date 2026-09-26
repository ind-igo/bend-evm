import { afterAll, beforeAll, expect, test } from 'bun:test';
import { bend, entries } from '../scripts/tools.js';
import { deploy, must, reverts } from './chain.js';

// Evm.view on a chain. The fixture is a small token too, so it reads itself.
const program = 'tests/fixtures/view/program.bend';
const alice = '0x00000000000000000000000000000000000a11ce';
const empty = '0x0000000000000000000000000000000000000e0a';
let chain;

beforeAll(async () => {
  chain = await deploy({ program, functions: entries.view });
  must(chain.send(chain.sender, 'mint(address,uint256)', alice, '30'));
  must(chain.send(chain.sender, 'mint(address,uint256)', chain.sender, '12'));
}, 120_000);

afterAll(() => chain?.stop());

test('a view call gives the word that the called function returns', () => {
  expect(chain.word('holding(address,uint256)(uint256)', chain.address, alice)).toBe(30n);
  expect(chain.word('others(address,address)(uint256)', chain.address, alice)).toBe(12n);
  expect(chain.word('others(address,address)(uint256)', chain.address, empty)).toBe(42n);
});

test('a view call reverts when the call fails or returns less than a word', () => {
  // The token's dispatcher rejects an address above 2^160; an account with no code returns nothing.
  reverts(chain.cast('call', chain.address, 'holding(address,uint256)(uint256)', chain.address, String(1n << 160n)));
  reverts(chain.cast('call', chain.address, 'holding(address,uint256)(uint256)', empty, alice));
});

test('a function that only makes view calls is view', () => {
  const abi = JSON.parse(must(bend('src/abi.bend', program, ...entries.view)));
  expect(abi.filter(f => f.type === 'function').map(f => [f.name, f.stateMutability])).toEqual([
    ['mint', 'nonpayable'], ['balanceOf', 'view'], ['totalSupply', 'view'], ['holding', 'view'], ['others', 'view']]);
}, 120_000);
