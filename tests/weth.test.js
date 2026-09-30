import { afterAll, beforeAll, expect, test } from 'bun:test';
import { bend, bytecode, entries } from '../scripts/tools.js';
import { deploy, must, run } from './chain.js';
import { generator } from './random.js';

// A differential test against Solidity. The Bend WETH (examples/weth) and
// solmate's WETH in Solidity (tests/fixtures/reference/WETH.sol) each get a
// Holder, which can refuse ether or call back into WETH when it gets
// ether. Both get the same random steps on one anvil chain, and must give
// the same results, logs and state after each step. Addresses become names
// first, as the two sides have their own. Only 4-byte revert data is
// compared, as Solidity panics where the Bend contract reverts with no
// data. SEED=<n> runs another sequence.
const seed = Number(process.env.SEED ?? 1);
const solidity = must(run('solc', '--evm-version', 'cancun', '--bin', 'tests/fixtures/reference/WETH.sol'));
const code = name => solidity.split(`:${name} =======`)[1].split('Binary:')[1].trim().split('\n')[0];
let chain, people, sides, names;

const create = (from, bytecode, args = '') =>
  JSON.parse(must(chain.cast('send', '--unlocked', '--from', from, '--json', '--create', '0x' + bytecode + args))).contractAddress;
const encode = address => address.slice(2).toLowerCase().padStart(64, '0');

beforeAll(async () => {
  chain = await deploy({ bytecode: bytecode(must(bend('src/compile.bend', 'examples/weth/WETH.bend', ...entries.weth))) });
  people = must(chain.cast('rpc', 'eth_accounts')).match(/0x[0-9a-fA-F]{40}/g).slice(0, 3);
  const ours = chain.address;
  const sol = create(people[0], code('WETH'));
  sides = [ours, sol].map(weth => ({ weth, holder: create(people[0], code('Holder'), encode(weth)) }));
  names = new Map([[ours, 'weth'], [sol, 'weth'], [sides[0].holder, 'holder'], [sides[1].holder, 'holder'],
    ...people.map((p, i) => [p, `person${i}`])].map(([a, n]) => [a.slice(2).toLowerCase(), n]));
}, 120_000);

afterAll(() => chain?.stop());

const named = text => [...names].reduce((t, [a, n]) => t.replaceAll(a, n), text.toLowerCase());

// JSON-RPC requests in one batch, with their results in order.
async function rpc(...requests) {
  const body = requests.map(([method, ...params], id) => ({ jsonrpc: '2.0', id, method, params }));
  const replies = await (await fetch(chain.rpc, { method: 'POST', headers: { 'content-type': 'application/json' },
    body: JSON.stringify(body) })).json();
  return replies.sort((a, b) => a.id - b.id);
}

const calldata = (signature, ...args) => signature ? must(run('cast', 'calldata', signature, ...args)) : '0x';
const hex = n => '0x' + n.toString(16);

// What one transaction did: "ok <returndata> <logs>" or "revert <error>".
// With no signature, the calldata is empty.
async function effect(from, to, value, signature, ...args) {
  const tx = { from, to, value: hex(value), data: calldata(signature, ...args) };
  const [call] = await rpc(['eth_call', tx, 'latest']);
  if (call.error) {
    expect(call.error.message).toMatch(/revert/i);
    const data = typeof call.error.data === 'string' ? call.error.data.slice(2) : '';
    return `revert ${data.length === 8 ? data : ''}`;
  }
  const [sent] = await rpc(['eth_sendTransaction', tx]);
  let receipt;
  while (!(receipt = (await rpc(['eth_getTransactionReceipt', sent.result]))[0].result)) await Bun.sleep(5);
  expect(receipt.status).toBe('0x1');
  return named(['ok', call.result, ...receipt.logs.map(l => `${l.address} ${l.topics.join(' ')} ${l.data}`)].join(' '));
}

const balanceOf = (weth, who) => ['eth_call', { to: weth, data: '0x70a08231' + who.slice(2).padStart(64, '0') }, 'latest'];

async function state({ weth, holder }) {
  const replies = await rpc(['eth_call', { to: weth, data: '0x18160ddd' }, 'latest'],
    ...[...people, holder].map(p => balanceOf(weth, p)), ['eth_getBalance', weth, 'latest'], ['eth_getBalance', holder, 'latest']);
  return ['state', ...replies.map(r => BigInt(r.result))].join(' ');
}

function steps(random, length) {
  const pick = xs => xs[Math.floor(random() * xs.length)];
  const amount = () => pick([0n, 1n, BigInt(Math.floor(random() * 1000)), BigInt(Math.floor(random() * 1000)) * 10n ** 15n]);
  const list = [];
  for (let i = 0; i < length; i++) {
    const who = pick(people);
    list.push(pick([
      { kind: 'deposit', who, value: amount() },
      { kind: 'receive', who, value: amount() },
      { kind: 'withdraw', who, amount: amount() },
      { kind: 'withdraw', who, amount: amount() },
      { kind: 'transfer', who, to: pick([...people, 'holder']), amount: amount(), value: pick([0n, 0n, 0n, 1n]) },
      { kind: 'hold', value: amount() },
      { kind: 'release', amount: amount() },
      { kind: 'release', amount: amount() },
      { kind: 'mode', mode: pick([0, 0, 1, 2, 3]) },
    ]));
  }
  return list;
}

// Steps that reach the paths that matter first: a refused send, and a
// holder that deposits again or withdraws again while it gets ether.
function scripted() {
  const release = amount => ({ kind: 'release', amount });
  const mode = m => ({ kind: 'mode', mode: m });
  return [
    { kind: 'hold', value: 10n ** 18n }, release(10n ** 17n),
    mode(1), release(10n ** 17n), mode(2), release(10n ** 17n), mode(3), release(10n ** 17n), mode(0),
    { kind: 'receive', who: people[1], value: 5n }, { kind: 'transfer', who: people[1], to: 'holder', amount: 1n, value: 1n },
  ];
}

// One step on one side, as lines of text.
async function apply({ weth, holder }, step) {
  switch (step.kind) {
    case 'deposit':
      return [await effect(step.who, weth, step.value, 'deposit()')];
    case 'receive':
      return [await effect(step.who, weth, step.value)];
    case 'withdraw':
      return [await effect(step.who, weth, 0n, 'withdraw(uint256)', String(step.amount))];
    case 'transfer':
      return [await effect(step.who, weth, step.value, 'transfer(address,uint256)', step.to === 'holder' ? holder : step.to,
        String(step.amount))];
    case 'hold':
      return [await effect(people[0], holder, step.value, 'deposit()')];
    case 'release':
      return [await effect(people[0], holder, 0n, 'withdraw(uint256)', String(step.amount))];
    case 'mode':
      return [await effect(people[0], holder, 0n, 'setMode(uint256)', String(step.mode))];
  }
}

test(`the Bend WETH and solmate's WETH agree on random steps (SEED=${seed})`, async () => {
  const list = [...scripted(), ...steps(generator(seed), 80)];
  const lines = sides.map(() => []);
  for (const step of list) {
    const text = JSON.stringify(step, (_, v) => typeof v === 'bigint' ? String(v) : v);
    for (const [i, side] of sides.entries()) lines[i].push(text, ...await apply(side, step), await state(side));
  }
  expect(lines[0]).toEqual(lines[1]);
  // The steps must reach the paths that matter: callbacks that deposit and
  // withdraw, a refused send, and ether sent to a function that is not payable.
  const all = lines[0].join('\n');
  const topic = event => must(run('cast', 'keccak', event)).slice(2);
  expect(all.split(`weth 0x${topic('Deposit(address,uint256)')} 0x000000000000000000000000holder`).length).toBeGreaterThan(3);
  expect(all.split(`weth 0x${topic('Withdrawal(address,uint256)')}`).length).toBeGreaterThan(10);
  expect(lines[0].filter(l => l === 'revert ').length).toBeGreaterThan(5);
}, 600_000);

test('the ABI marks deposit and receive payable', () => {
  const abi = JSON.parse(must(bend('src/abi.bend', 'examples/weth/WETH.bend', ...entries.weth)));
  expect(abi.find(item => item.name === 'deposit').stateMutability).toBe('payable');
  expect(abi.find(item => item.name === 'withdraw').stateMutability).toBe('nonpayable');
  expect(abi.filter(item => item.type === 'receive')).toEqual([{ type: 'receive', stateMutability: 'payable' }]);
}, 120_000);
