import { afterAll, beforeAll, expect, test } from 'bun:test';
import { bend, entries } from '../scripts/tools.js';
import { deploy, must, run } from './chain.js';

// Bytes and strings (tests/fixtures/bytes) against the same functions in
// Solidity (tests/fixtures/bytes/Reference.sol): results, revert data and
// logs must be the same for each value, and a Receiver gets the same bytes
// and calls back with them. The dispatcher also rejects calldata that
// Solidity accepts: an offset that is not a multiple of 32, and padding
// that is not zero.
const solidity = must(run('solc', '--evm-version', 'cancun', '--bin', 'tests/fixtures/bytes/Reference.sol'));
const code = name => solidity.split(`:${name} =======`)[1].split('Binary:')[1].trim().split('\n')[0];
let chain, sides;

const create = bytecode =>
  JSON.parse(must(chain.cast('send', '--unlocked', '--from', chain.sender, '--json', '--create', '0x' + bytecode))).contractAddress;

beforeAll(async () => {
  chain = await deploy({ program: 'tests/fixtures/bytes/program.bend', functions: entries.bytes });
  sides = [chain.address, create(code('Reference'))].map(contract => ({ contract, receiver: create(code('Receiver')) }));
}, 120_000);

afterAll(() => chain?.stop());

async function rpc(method, ...params) {
  const reply = await (await fetch(chain.rpc, { method: 'POST', headers: { 'content-type': 'application/json' },
    body: JSON.stringify({ jsonrpc: '2.0', id: 1, method, params }) })).json();
  return reply;
}

// The result of an eth_call: "ok <data>" or "revert <data>".
async function call(to, data) {
  const reply = await rpc('eth_call', { from: chain.sender, to, data }, 'latest');
  if (reply.error) {
    expect(reply.error.message).toMatch(/revert/i);
    return `revert ${typeof reply.error.data === 'string' ? reply.error.data : ''}`;
  }
  return `ok ${reply.result}`;
}

const calldata = (signature, ...args) => must(run('cast', 'calldata', signature, ...args));

// Byte values around the word size, with bytes that are not zero.
const lengths = [0, 1, 2, 31, 32, 33, 63, 64, 65, 100];
const values = lengths.map(n => '0x' + Array.from({ length: n }, (_, i) => ((i * 37 + n) % 255 + 1).toString(16).padStart(2, '0')).join(''));
const texts = ['', 'a', 'hello', 'héllo ✓', 'x'.repeat(32), 'y'.repeat(70)];

test('each function gives what Solidity gives', async () => {
  for (const data of values) {
    for (const signature of ['echo(bytes)', 'size(bytes)', 'hash(bytes)']) {
      const input = calldata(signature, data);
      const [ours, theirs] = await Promise.all(sides.map(s => call(s.contract, input)));
      expect(ours).toBe(theirs);
    }
  }
  for (const text of texts) {
    for (const code of ['0', '7']) {
      const input = calldata('refuse(uint256,string)', code, text);
      const [ours, theirs] = await Promise.all(sides.map(s => call(s.contract, input)));
      expect(ours).toBe(theirs);
    }
  }
  expect(await call(sides[0].contract, calldata('size(bytes)', values[3]))).toBe('ok 0x' + 31n.toString(16).padStart(64, '0'));
}, 120_000);

// The logs of a transaction, with each side's addresses as names.
function logs({ contract, receiver }, signature, ...args) {
  const receipt = JSON.parse(must(chain.cast('send', '--unlocked', '--from', chain.sender, '--json', contract, signature, ...args)));
  expect(receipt.status).toBe('0x1');
  const name = text => text.toLowerCase().replaceAll(contract.slice(2).toLowerCase(), 'contract')
    .replaceAll(receiver.slice(2).toLowerCase(), 'receiver');
  return receipt.logs.map(l => name(`${l.address} ${l.topics.join(' ')} ${l.data}`));
}

test('logs and calls with bytes are the same as in Solidity', () => {
  for (const [i, data] of values.entries()) {
    const text = texts[i % texts.length];
    const [ours, theirs] = sides.map(s => logs(s, 'note(uint256,string,bytes)', String(i), text, data));
    expect(ours).toEqual(theirs);
    expect(ours.length).toBe(1);
  }
  // forward calls the Receiver, which calls note back with the same bytes.
  for (const data of values) {
    const [ours, theirs] = sides.map(s => logs(s, 'forward(address,bytes)', s.receiver, data));
    expect(ours).toEqual(theirs);
    expect(ours[0]).toContain(data.slice(2).toLowerCase());
  }
}, 300_000);

test('the dispatcher rejects bytes that are not well encoded', async () => {
  const good = calldata('size(bytes)', '0x' + 'ab'.repeat(3));
  const word = i => good.slice(10 + 64 * i, 10 + 64 * (i + 1));
  const with_ = (...words) => good.slice(0, 10) + words.join('');
  const hex = n => n.toString(16).padStart(64, '0');
  expect(await call(sides[0].contract, good)).toBe('ok 0x' + hex(3));
  // An offset that is not a multiple of 32.
  expect(await call(sides[0].contract, with_(hex(33), '00', word(1), word(2)))).toBe('revert 0x');
  // Padding that is not zero.
  const dirty = word(2).slice(0, 62) + '01';
  expect(await call(sides[0].contract, with_(word(0), word(1), dirty))).toBe('revert 0x');
  expect(await call(sides[1].contract, with_(word(0), word(1), dirty))).toBe('ok 0x' + hex(3));
  // Bytes that end past the calldata, and an offset past it.
  expect(await call(sides[0].contract, with_(word(0), hex(40), word(2)))).toBe('revert 0x');
  expect(await call(sides[0].contract, with_(hex(1n << 40n)))).toBe('revert 0x');
  // A head that is missing.
  expect(await call(sides[0].contract, good.slice(0, 10))).toBe('revert 0x');
}, 60_000);

test('the ABI gives bytes and string types', () => {
  const abi = JSON.parse(must(bend('src/abi.bend', 'tests/fixtures/bytes/program.bend', ...entries.bytes)));
  expect(abi.find(item => item.name === 'note').inputs).toEqual([{ name: 'id', type: 'uint256' },
    { name: 'text', type: 'string' }, { name: 'data', type: 'bytes' }]);
  expect(abi.find(item => item.name === 'echo').outputs).toEqual([{ name: 'data', type: 'bytes' }, { name: 'size', type: 'uint256' }]);
  expect(abi.find(item => item.type === 'event' && item.name === 'Note').inputs.map(i => i.type)).toEqual(['uint256', 'string', 'bytes']);
  expect(abi.find(item => item.type === 'error').inputs).toEqual([{ name: 'code', type: 'uint256' }, { name: 'reason', type: 'string' }]);
}, 120_000);
