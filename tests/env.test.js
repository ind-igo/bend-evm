import { afterAll, beforeAll, expect, test } from 'bun:test';
import { entries } from '../scripts/tools.js';
import { deploy, must, run } from './chain.js';

// The values of the environment (tests/fixtures/env) against what anvil
// gives for the same block, transaction and accounts. Each entry but block
// returns its value, which reading it last makes a Yul.Sensed; block reads
// the block's values into locals, each a Yul.Sense, and logs them.
let chain, block;
const coinbase = '0x00000000000000000000000000000000000c0ffe';
const stranger = '0x000000000000000000000000000000000000beef';

beforeAll(async () => {
  chain = await deploy({ program: 'tests/fixtures/env/program.bend', functions: entries.env });
  must(chain.cast('rpc', 'anvil_setCoinbase', coinbase));
  must(chain.cast('rpc', 'anvil_setBalance', chain.address, '0x3039'));
  must(chain.cast('rpc', 'anvil_setBalance', stranger, '0x7'));
  must(chain.cast('rpc', 'anvil_mine'));
  block = JSON.parse(must(chain.cast('block', 'latest', '--json')));
}, 120_000);

afterAll(() => chain?.stop());

// An eth_call on the latest block, with the given transaction fields.
async function value(signature, args = [], fields = {}) {
  const data = must(run('cast', 'calldata', signature, ...args.map(String)));
  const reply = await (await fetch(chain.rpc, { method: 'POST', headers: { 'content-type': 'application/json' },
    body: JSON.stringify({ jsonrpc: '2.0', id: 1, method: 'eth_call',
      params: [{ to: chain.address, data, ...fields }, 'latest'] }) })).json();
  expect(reply.error).toBeUndefined();
  return BigInt(reply.result);
}

const hex = x => BigInt(x);
const keccak = code => BigInt(must(run('cast', 'keccak', code)));

test('the values of the block', async () => {
  expect(block.excessBlobGas).toBe('0x0');
  expect(await value('timestamp()')).toBe(hex(block.timestamp));
  expect(await value('number()')).toBe(hex(block.number));
  expect(await value('coinbase()')).toBe(hex(coinbase));
  expect(await value('prevrandao()')).toBe(hex(block.mixHash));
  expect(await value('gaslimit()')).toBe(hex(block.gasLimit));
  expect(await value('basefee()')).toBe(hex(block.baseFeePerGas));
  // With no excess blob gas, the blob base fee is its least value.
  expect(await value('blobbasefee()')).toBe(1n);
  expect(await value('chainid()')).toBe(BigInt(must(chain.cast('chain-id'))));
  const parent = JSON.parse(must(chain.cast('block', String(hex(block.number) - 1n), '--json')));
  expect(await value('blockhash(uint256)', [hex(block.number) - 1n])).toBe(hex(parent.hash));
  expect(await value('blockhash(uint256)', [hex(block.number)])).toBe(0n);
  expect(await value('blobhash(uint256)', [0])).toBe(0n);
}, 60_000);

test('the values of the transaction', async () => {
  expect(await value('origin()', [], { from: stranger })).toBe(hex(stranger));
  expect(await value('gasprice()', [], { from: chain.sender, gasPrice: '0x77359400' })).toBe(2_000_000_000n);
  // The gas left is the limit less the 21000 of every transaction and a little more.
  const gas = await value('gas()', [], { gas: '0x186a0' });
  expect(gas < 79_000n && gas > 70_000n).toBe(true);
}, 60_000);

test('the values of the accounts', async () => {
  const code = must(chain.cast('code', chain.address));
  expect(await value('codesize()')).toBe(BigInt((code.length - 2) / 2));
  expect(await value('selfbalance()')).toBe(12345n);
  expect(await value('balance(uint256)', [hex(stranger)])).toBe(7n);
  expect(await value('balance(uint256)', [hex(chain.address)])).toBe(12345n);
  expect(await value('extcodesize(uint256)', [hex(chain.address)])).toBe(BigInt((code.length - 2) / 2));
  expect(await value('extcodesize(uint256)', [hex(stranger)])).toBe(0n);
  expect(await value('extcodehash(uint256)', [hex(chain.address)])).toBe(keccak(code));
  // An account with a balance and no code has the hash of no code; one that does not exist has 0.
  expect(await value('extcodehash(uint256)', [hex(stranger)])).toBe(keccak('0x'));
  expect(await value('extcodehash(uint256)', [0xdeadn])).toBe(0n);
}, 60_000);

test('block logs the values of its block and transaction', () => {
  const receipt = JSON.parse(must(chain.cast('send', '--unlocked', '--from', chain.sender, '--json', chain.address, 'block()')));
  const mined = JSON.parse(must(chain.cast('block', String(hex(receipt.blockNumber)), '--json')));
  const [log] = receipt.logs;
  expect(log.topics).toEqual([must(run('cast', 'keccak',
    'Block(uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256)'))]);
  const words = log.data.slice(2).match(/.{64}/g).map(w => BigInt('0x' + w));
  expect(words).toEqual([hex(mined.timestamp), hex(mined.number), hex(coinbase), hex(mined.mixHash), hex(mined.gasLimit),
    hex(mined.baseFeePerGas), 1n, hex(receipt.effectiveGasPrice), hex(chain.sender)]);
}, 60_000);
