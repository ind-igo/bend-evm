import { afterAll, beforeAll, expect, test } from 'bun:test';
import { entries, top } from '../scripts/tools.js';
import { deploy, must, run } from './chain.js';
import { generator } from './random.js';
import { keys, separator, sign } from './permit.js';

// A differential test against Solidity. The Bend token and the same token in
// Solidity with solmate's logic (tests/fixtures/reference/Token.sol) get the
// same random calls on one anvil chain. Both must succeed or both revert,
// return the same bytes, and log the same events. Words span 256 bits, so
// this reaches the overflow boundary. Revert data may differ: Solidity's
// arithmetic reverts with Panic(0x11), and Bend reverts with no data.
// SEED=<n> runs another sequence.
const seed = Number(process.env.SEED ?? 1);
// The deployer and three accounts that can sign permits.
const people = ['0x0000000000000000000000000000000000001001', ...Object.keys(keys)];
const permit = 'permit(address,address,uint256,uint256,uint8,bytes32,bytes32)';
const views = new Set(['name()', 'symbol()', 'decimals()', 'owner()', 'totalSupply()', 'balanceOf(address)',
  'allowance(address,address)', 'nonces(address)', 'DOMAIN_SEPARATOR()']);

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
    [a, permit, b, c, '9', 'later', 'owner'],
    [a, 'allowance(address,address)', b, c],
    [a, permit, b, c, '9', 'later', 'owner'],
    [a, permit, b, c, '9', 'earlier', 'owner'],
    [a, permit, b, c, '9', 'later', 'other'],
    [a, permit, b, c, '9', 'later', 'junk'],
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
      [who, pick(['name()', 'symbol()', 'decimals()', 'DOMAIN_SEPARATOR()'])],
      [who, 'nonces(address)', a],
      [who, permit, pick(people.slice(1)), b, amount(), pick(['later', 'later', 'earlier']), pick(['owner', 'owner', 'other', 'junk'])],
      [pick(people), 'transferOwnership(address)', a],
    ]));
  }
  return calls;
}

// A transaction's logs, as text.
const logs = receipt => receipt.logs.map(log => `log ${log.topics.join(' ')} ${log.data}`);
let chain, solidity, created;

beforeAll(async () => {
  const supply = BigInt(Math.floor(generator(seed)() * 1000));
  chain = await deploy({ program: 'examples/token/program.bend', functions: entries.token, deployer: people[0],
    args: [supply] });
  for (const who of people.slice(1)) chain.fund(who);
  const out = must(run('solc', '--evm-version', 'shanghai', '--bin', 'tests/fixtures/reference/Token.sol'));
  const bytecode = out.split('Binary:')[1].trim();
  const args = must(run('cast', 'abi-encode', 'constructor(uint256)', String(supply))).slice(2);
  created = JSON.parse(must(chain.cast('send', '--unlocked', '--from', people[0], '--json', '--create',
    '0x' + bytecode + args)));
  solidity = created.contractAddress;
}, 120_000);

afterAll(() => chain?.stop());

let now, chainId;

// A permit's words for one contract: signed over that contract's domain, for
// the nonce that the Solidity reference reports, by the owner, by another
// account, or not at all.
function permitArgs(address, [owner, spender, value, when, signer]) {
  const deadline = String(when === 'later' ? now + 100000 : now - 100000);
  if (signer === 'junk') return [owner, spender, value, deadline, '27', '0x' + '11'.repeat(32), '0x' + '22'.repeat(32)];
  const nonce = BigInt(must(chain.cast('call', solidity, 'nonces(address)(uint256)', owner)).split(' ')[0]);
  const key = keys[signer === 'owner' ? owner : Object.keys(keys).find(k => k !== owner)];
  const domain = separator('Bend Token', chainId, address);
  return [owner, spender, value, deadline, ...sign(key, domain, owner, spender, value, nonce, deadline)];
}

// What one contract did: "ok <returndata>" or "revert", then its logs.
function effect(address, [from, signature, ...rest]) {
  const args = signature === permit ? permitArgs(address, rest) : rest;
  const call = chain.cast('call', '--from', from, address, signature, ...args);
  if (!call.ok) {
    expect(call.err).toMatch(/revert/i);
    return ['revert'];
  }
  if (signature === 'DOMAIN_SEPARATOR()') return ['ok ' + (call.out === separator('Bend Token', chainId, address))];
  if (views.has(signature)) return ['ok ' + call.out];
  const receipt = JSON.parse(must(chain.cast('send', '--unlocked', '--from', from, '--json', address, signature, ...args)));
  expect(receipt.status).toBe('0x1');
  return ['ok ' + call.out, ...logs(receipt)];
}

test(`the Bend token and the Solidity token agree on random calls (SEED=${seed})`, () => {
  now = Number(must(chain.cast('block', 'latest', '--field', 'timestamp')));
  chainId = must(chain.cast('chain-id'));
  const calls = [...scripted(), ...sequence(generator(seed), 120)];
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
