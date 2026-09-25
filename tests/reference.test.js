import { afterAll, beforeAll, expect, test } from 'bun:test';
import { deploy, must, run } from './chain.js';
import { generator } from './random.js';

// A differential test against Solidity. The Bend token and the same token in
// Solidity with solmate's logic (tests/fixtures/reference/Token.sol) get the
// same random calls on one anvil chain. Both must succeed or both revert,
// return the same bytes, and log the same events. Words span 256 bits, so
// this reaches the overflow boundary. Revert data may differ: Solidity's
// arithmetic reverts with Panic(0x11), and Bend reverts with no data.
// SEED=<n> runs another sequence.
const seed = Number(process.env.SEED ?? 1);
const top = (1n << 256n) - 1n;
const people = ['0x0000000000000000000000000000000000001001', '0x0000000000000000000000000000000000001002',
  '0x0000000000000000000000000000000000001003', '0x0000000000000000000000000000000000001004'];
const functions = ['name', 'symbol', 'decimals', 'init', 'owner', 'transferOwnership', 'totalSupply', 'balanceOf',
  'transfer', 'mint', 'burn', 'allowance', 'approve', 'transferFrom'];
const views = new Set(['name()', 'symbol()', 'decimals()', 'owner()', 'totalSupply()', 'balanceOf(address)',
  'allowance(address,address)']);

// Calls that reach the paths that matter, before the random ones.
function scripted() {
  const [a, b, c, d] = people;
  return [
    [a, 'mint(address,uint256)', b, '100'],
    [b, 'approve(address,uint256)', c, String(top)],
    [c, 'transferFrom(address,address,uint256)', b, d, '30'],
    [c, 'allowance(address,address)', b, c],
    [b, 'approve(address,uint256)', c, '10'],
    [c, 'transferFrom(address,address,uint256)', b, d, '11'],
    [c, 'transferFrom(address,address,uint256)', b, d, '10'],
    [c, 'allowance(address,address)', b, c],
    [a, 'mint(address,uint256)', d, String(top)],
    [d, 'transfer(address,uint256)', d, '40'],
    [d, 'burn(uint256)', '41'],
    [d, 'burn(uint256)', '1'],
    [b, 'transferOwnership(address)', b],
    [a, 'transferOwnership(address)', b],
    [b, 'mint(address,uint256)', a, '5'],
  ];
}

function sequence(random, length) {
  const pick = xs => xs[Math.floor(random() * xs.length)];
  const big = () => BigInt('0x' + Array.from({ length: 64 }, () => Math.floor(random() * 16).toString(16)).join(''));
  const amount = () => String(random() < 0.7 ? BigInt(Math.floor(random() * 60))
    : pick([top, top - BigInt(Math.floor(random() * 60)), 1n << 255n, big()]));
  const calls = [];
  for (let i = 0; i < length; i++) {
    const who = pick(people), a = pick(people), b = pick(people);
    calls.push(pick([
      [who, 'mint(address,uint256)', a, amount()],
      [pick(people), 'mint(address,uint256)', a, amount()],
      [who, 'transfer(address,uint256)', a, amount()],
      [who, 'transfer(address,uint256)', a, amount()],
      [who, 'approve(address,uint256)', a, amount()],
      [who, 'transferFrom(address,address,uint256)', a, b, amount()],
      [who, 'transferFrom(address,address,uint256)', a, b, amount()],
      [who, 'burn(uint256)', amount()],
      [who, 'balanceOf(address)', a],
      [who, 'allowance(address,address)', a, b],
      [who, 'totalSupply()'],
      [who, 'owner()'],
      [who, pick(['name()', 'symbol()', 'decimals()'])],
      [pick(people), 'transferOwnership(address)', a],
    ]));
  }
  return calls;
}

let chain, solidity, created;

beforeAll(async () => {
  const supply = BigInt(Math.floor(generator(seed)() * 1000));
  chain = await deploy('examples/token/program.bend', functions, { deployer: people[0], args: [supply] });
  for (const who of people.slice(1)) chain.fund(who);
  const out = must(run('solc', '--evm-version', 'shanghai', '--bin', 'tests/fixtures/reference/Token.sol'));
  const bytecode = out.split('Binary:')[1].trim();
  const args = must(run('cast', 'abi-encode', 'constructor(uint256)', String(supply))).slice(2);
  created = JSON.parse(must(chain.cast('send', '--unlocked', '--from', people[0], '--json', '--create',
    '0x' + bytecode + args)));
  solidity = created.contractAddress;
}, 120_000);

afterAll(() => chain?.stop());

// What one contract did: "ok <returndata>" or "revert", then its logs.
function effect(address, [from, signature, ...args]) {
  const call = chain.cast('call', '--from', from, address, signature, ...args);
  if (!call.ok) {
    expect(call.err).toMatch(/revert/i);
    return ['revert'];
  }
  if (views.has(signature)) return ['ok ' + call.out];
  const receipt = JSON.parse(must(chain.cast('send', '--unlocked', '--from', from, '--json', address, signature, ...args)));
  expect(receipt.status).toBe('0x1');
  return ['ok ' + call.out, ...receipt.logs.map(log => `log ${log.topics.join(' ')} ${log.data}`)];
}

test(`the Bend token and the Solidity token agree on random calls (SEED=${seed})`, () => {
  const calls = [...scripted(), ...sequence(generator(seed), 120)];
  const logs = receipt => receipt.logs.map(log => `log ${log.topics.join(' ')} ${log.data}`);
  const bend = ['deploy', ...logs(chain.receipt)], sol = ['deploy', ...logs(created)];
  for (const call of calls) {
    bend.push(call.join(' '), ...effect(chain.address, call));
    sol.push(call.join(' '), ...effect(solidity, call));
  }
  expect(bend).toEqual(sol);
  const text = bend.join('\n');
  expect(text).toMatch(/revert/);
  expect(text.match(/^ok 0x0*1$/gm)?.length).toBeGreaterThan(5);
}, 300_000);
