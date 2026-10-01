import { afterAll, beforeAll, expect, test } from 'bun:test';
import { bend, bytecode, entries } from '../scripts/tools.js';
import { deploy, must, run } from './chain.js';
import { generator } from './random.js';

// A differential test against Solidity. The Bend auction (examples/auction)
// and SimpleAuction from the Solidity documentation
// (tests/fixtures/reference/Auction.sol) each get a Bidder, which can refuse
// ether or call back into the auction when it gets ether, and a
// beneficiary of their own. Both get the same random steps on one anvil
// chain, and must give the same results, logs and state after each step.
// The auctions end at the same time; a wait step moves the chain's time past
// the end, for both at once. Addresses become names first, as the two sides
// have their own. A Solidity panic counts as a revert with no data, as the
// Bend contract gives. SEED=<n> runs another sequence.
const seed = Number(process.env.SEED ?? 1);
const solidity = must(run('solc', '--evm-version', 'cancun', '--bin', 'tests/fixtures/reference/Auction.sol'));
const code = name => solidity.split(`:${name} =======`)[1].split('Binary:')[1].trim().split('\n')[0];
const biddingTime = 100_000n;
// Accounts with no code, which only get ether.
const beneficiaries = ['0x000000000000000000000000000000000000bee1', '0x000000000000000000000000000000000000bee2'];
let chain, people, sides, names;

const word = x => BigInt(x).toString(16).padStart(64, '0');
const create = (from, bytecode, args = '') =>
  JSON.parse(must(chain.cast('send', '--unlocked', '--from', from, '--json', '--create', '0x' + bytecode + args))).contractAddress;

beforeAll(async () => {
  const program = bytecode(must(bend('src/compile.bend', 'examples/auction/Auction.bend', ...entries.auction)));
  chain = await deploy({ bytecode: program, args: [biddingTime, BigInt(beneficiaries[0])] });
  people = must(chain.cast('rpc', 'eth_accounts')).match(/0x[0-9a-fA-F]{40}/g).slice(0, 3);
  const ours = chain.address;
  // The Solidity auction starts one second later, so it ends at the same time.
  const start = BigInt(JSON.parse(must(chain.cast('block', String(chain.receipt.blockNumber), '--json'))).timestamp);
  must(chain.cast('rpc', 'evm_setNextBlockTimestamp', String(start + 1n)));
  const sol = create(people[0], code('SimpleAuction'), word(biddingTime - 1n) + word(beneficiaries[1]));
  sides = [[ours, beneficiaries[0]], [sol, beneficiaries[1]]].map(([auction, beneficiary]) =>
    ({ auction, beneficiary, bidder: create(people[0], code('Bidder'), word(auction)) }));
  names = new Map([...sides.flatMap(s => [[s.auction, 'auction'], [s.bidder, 'bidder'], [s.beneficiary, 'beneficiary']]),
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

const calldata = (signature, ...args) => must(run('cast', 'calldata', signature, ...args));
const hex = n => '0x' + n.toString(16);

// What one transaction did: "ok <returndata> <logs>" or "revert <data>".
async function effect(from, to, value, signature, ...args) {
  const tx = { from, to, value: hex(value), data: calldata(signature, ...args) };
  const [call] = await rpc(['eth_call', tx, 'latest']);
  if (call.error) {
    expect(call.error.message).toMatch(/revert/i);
    const data = typeof call.error.data === 'string' ? call.error.data.slice(2) : '';
    return `revert ${data.startsWith('4e487b71') ? '' : data}`;
  }
  const [sent] = await rpc(['eth_sendTransaction', tx]);
  let receipt;
  while (!(receipt = (await rpc(['eth_getTransactionReceipt', sent.result]))[0].result)) await Bun.sleep(5);
  expect(receipt.status).toBe('0x1');
  return named(['ok', call.result, ...receipt.logs.map(l => `${l.address} ${l.topics.join(' ')} ${l.data}`)].join(' '));
}

const view = (to, signature, ...args) => ['eth_call', { to, data: calldata(signature, ...args) }, 'latest'];

async function state({ auction, bidder, beneficiary }) {
  const replies = await rpc(view(auction, 'status()'), view(auction, 'auctionEndTime()'),
    ...[...people, bidder].map(p => view(auction, 'pendingReturns(address)', p)),
    ...[auction, bidder, beneficiary].map(a => ['eth_getBalance', a, 'latest']));
  return named(['state', ...replies.map(r => r.result)].join(' '));
}

function steps(random, length, first) {
  const pick = xs => xs[Math.floor(random() * xs.length)];
  // Bids that grow along the steps, so many of them lead, and small ones.
  const amount = i => pick([0n, 1n, BigInt(Math.floor(random() * 1000)), BigInt(first + i) * 10n ** 16n + BigInt(Math.floor(random() * 1000))]);
  const list = [];
  for (let i = 0; i < length; i++) {
    const who = pick(people);
    list.push(pick([
      { kind: 'bid', who, value: amount(i) },
      { kind: 'bid', who, value: amount(i) },
      { kind: 'withdraw', who },
      { kind: 'hold', value: amount(i) },
      { kind: 'release' },
      { kind: 'release' },
      { kind: 'end', who },
      { kind: 'mode', mode: pick([0, 0, 1, 2, 3]) },
    ]));
  }
  return list;
}

// Steps that reach the paths that matter first: a refused send, and a
// bidder that withdraws again or bids again while it gets ether.
function scripted() {
  const e = n => BigInt(n) * 10n ** 16n;
  const mode = m => ({ kind: 'mode', mode: m });
  const release = { kind: 'release' };
  return [
    { kind: 'end', who: people[0] }, { kind: 'hold', value: e(1) }, { kind: 'bid', who: people[1], value: e(1) },
    { kind: 'bid', who: people[1], value: e(2) }, mode(1), release, mode(2), release, { kind: 'hold', value: e(3) },
    { kind: 'bid', who: people[2], value: e(4) }, mode(3), release, mode(0), release,
  ];
}

// One step on one side, as lines of text.
async function apply({ auction, bidder }, step) {
  switch (step.kind) {
    case 'bid':
      return [await effect(step.who, auction, step.value, 'bid()')];
    case 'withdraw':
      return [await effect(step.who, auction, 0n, 'withdraw()')];
    case 'end':
      return [await effect(step.who, auction, 0n, 'auctionEnd()')];
    case 'hold':
      return [await effect(people[0], bidder, step.value, 'bid()')];
    case 'release':
      return [await effect(people[0], bidder, 0n, 'withdraw()')];
    case 'mode':
      return [await effect(people[0], bidder, 0n, 'setMode(uint256)', String(step.mode))];
  }
}

test(`the Bend auction and Solidity's SimpleAuction agree on random steps (SEED=${seed})`, async () => {
  const random = generator(seed);
  const before = [...scripted(), ...steps(random, 60, 5)];
  const after = [{ kind: 'end', who: people[0] }, { kind: 'end', who: people[1] }, ...steps(random, 30, 70)];
  const lines = sides.map(() => []);
  const play = async list => {
    for (const step of list) {
      const text = JSON.stringify(step, (_, v) => typeof v === 'bigint' ? String(v) : v);
      for (const [i, side] of sides.entries()) lines[i].push(text, ...await apply(side, step), await state(side));
    }
  };
  await play(before);
  await rpc(['evm_increaseTime', Number(2n * biddingTime)], ['evm_mine']);
  await play(after);
  expect(lines[0]).toEqual(lines[1]);
  // The steps must reach the paths that matter: each error, refused sends,
  // and an end that pays the beneficiary.
  const all = lines[0].join('\n');
  const selector = error => must(run('cast', 'sig', error)).slice(2);
  for (const error of ['AuctionAlreadyEnded()', 'BidNotHighEnough(uint256)', 'AuctionNotYetEnded()', 'AuctionEndAlreadyCalled()'])
    expect(all).toContain(`revert ${selector(error)}`);
  expect(lines[0].filter(l => l === 'revert ').length).toBeGreaterThan(0);
  const topic = event => must(run('cast', 'keccak', event)).slice(2);
  expect(all.split(`auction 0x${topic('HighestBidIncreased(address,uint256)')}`).length).toBeGreaterThan(10);
  expect(all.split(`auction 0x${topic('AuctionEnded(address,uint256)')}`).length).toBe(2);
}, 600_000);

test('the ABI gives status as a named tuple and marks bid payable', () => {
  const abi = JSON.parse(must(bend('src/abi.bend', 'examples/auction/Auction.bend', ...entries.auction)));
  expect(abi.find(item => item.name === 'bid').stateMutability).toBe('payable');
  expect(abi.find(item => item.name === 'withdraw').stateMutability).toBe('nonpayable');
  expect(abi.find(item => item.name === 'status').outputs.map(o => `${o.type} ${o.name}`))
    .toEqual(['address highestBidder', 'uint256 highestBid', 'bool ended']);
  expect(abi.find(item => item.type === 'constructor').inputs.map(i => `${i.type} ${i.name}`))
    .toEqual(['uint256 biddingTime', 'address beneficiaryAddress']);
}, 120_000);
