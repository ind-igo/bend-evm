import { afterAll, beforeAll, expect, test } from 'bun:test';
import { deploy, must, run } from './chain.js';

// A differential test: random calls run on the token's Bend source and on
// the compiled token on anvil must give the same returns, reverts and logs.
// It tests what the proofs do not cover: the printer, the dispatcher, the
// topics and solc. (token.test.js checks the storage layout.) The Bend runtime holds words below
// 2^48, so the model's limit is 2^40 and amounts stay small, so no sum comes
// near it. The model's max(), 2^40 - 1, stands for the EVM's 2^256 - 1, and
// only approve uses it. SEED=<n> runs another sequence.
const limit = 1n << 40n;
const top = (1n << 256n) - 1n;
const toChain = x => x === limit - 1n ? top : x;
const fromChain = x => x === top ? limit - 1n : x;
const seed = Number(process.env.SEED ?? 1);
const people = [0x1001n, 0x1002n, 0x1003n, 0x1004n];
const address = x => '0x' + x.toString(16).padStart(40, '0');

// The ABI signature of each function, and which of its words are addresses.
const functions = {
  owner: ['owner()(uint256)', []],
  transferOwnership: ['transferOwnership(address)', [true]],
  totalSupply: ['totalSupply()(uint256)', []],
  balanceOf: ['balanceOf(address)(uint256)', [true]],
  transfer: ['transfer(address,uint256)(uint256)', [true, false]],
  mint: ['mint(address,uint256)', [true, false]],
  allowance: ['allowance(address,address)(uint256)', [true, true]],
  approve: ['approve(address,uint256)(uint256)', [true, false]],
  transferFrom: ['transferFrom(address,address,uint256)(uint256)', [true, true, false]],
};
const views = new Set(['owner', 'totalSupply', 'balanceOf', 'allowance']);
const events = Object.fromEntries(['Transfer(address,address,uint256)', 'Approval(address,address,uint256)',
  'OwnershipTransferred(address,address)'].map(e => [must(run('cast', 'keccak', e)), e]));

// mulberry32: a small seeded generator, so a failing sequence repeats.
function generator(state) {
  return () => {
    state = (state + 0x6D2B79F5) | 0;
    let t = Math.imul(state ^ (state >>> 15), 1 | state);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function sequence(random, length) {
  const pick = xs => xs[Math.floor(random() * xs.length)];
  const amount = () => BigInt(Math.floor(random() * 60));
  const calls = [];
  for (let i = 0; i < length; i++) {
    const who = pick(people), a = pick(people), b = pick(people);
    calls.push(pick([
      { who, name: 'mint', args: [a, amount()] },
      { who: pick(people), name: 'mint', args: [a, amount()] },
      { who: pick(people), name: 'mint', args: [a, amount()] },
      { who, name: 'transfer', args: [a, amount()] },
      { who, name: 'transfer', args: [a, amount()] },
      { who, name: 'approve', args: [a, random() < 0.5 ? limit - 1n : amount()] },
      { who, name: 'transferFrom', args: [a, b, amount()] },
      { who, name: 'transferFrom', args: [a, b, amount()] },
      { who, name: 'balanceOf', args: [a] },
      { who, name: 'allowance', args: [a, b] },
      { who, name: 'totalSupply', args: [] },
      { who, name: 'owner', args: [] },
      { who: pick([people[0], who]), name: 'transferOwnership', args: [a] },
    ]));
  }
  return calls;
}

// The model's transcript: one "ok", "ok <word>" or "revert" line per call,
// each followed by its logs.
function model(calls) {
  const words = calls.flatMap(({ who, name, args }) =>
    [who, name, ...[...args, 0n, 0n, 0n].slice(0, 3)].map(String));
  const result = run(process.execPath, 'vendor/bend-frontend/host/run.js', 'tests/fixtures/model/token.bend',
    String(limit), ...words);
  return must(result).split('\n');
}

// The same transcript, read from anvil.
function logs(receipt) {
  return receipt.logs.map(log => {
    expect(log.address.toLowerCase()).toBe(chain.address.toLowerCase());
    const [event, ...topics] = log.topics;
    const data = (log.data.slice(2).match(/.{64}/g) ?? []).map(w => fromChain(BigInt('0x' + w)));
    return `log ${events[event]}${topics.map(t => ' ' + BigInt(t)).join('')} |${data.map(d => ' ' + d).join('')}`;
  });
}

function onChain({ who, name, args }) {
  const [signature, kinds] = functions[name];
  const words = args.map((x, i) => kinds[i] ? address(x) : String(toChain(x)));
  const from = address(who);
  const call = chain.cast('call', '--from', from, chain.address, signature, ...words);
  if (!call.ok) {
    expect(call.err).toMatch(/revert/i);
    return ['revert'];
  }
  const value = call.out === '' || call.out === '0x' ? '' : ' ' + fromChain(BigInt(call.out.split(' ')[0]));
  if (views.has(name)) return ['ok' + value];
  const receipt = JSON.parse(must(chain.cast('send', '--unlocked', '--from', from, '--json', chain.address,
    signature.replace(/\)\(.*\)$/, ')'), ...words)));
  expect(receipt.status).toBe('0x1');
  return ['ok' + value, ...logs(receipt)];
}

const supply = 1n + BigInt(Math.floor(generator(seed)() * 100));
let chain;

beforeAll(async () => {
  chain = await deploy('examples/token/program.bend', ['init', ...Object.keys(functions)],
    { deployer: address(people[0]), args: [supply] });
  for (const who of people.slice(1)) chain.fund(address(who));
}, 120_000);

afterAll(() => chain?.stop());

test(`anvil agrees with the Bend model on random calls (SEED=${seed})`, () => {
  const calls = sequence(generator(seed), 120);
  const expected = model([{ who: people[0], name: 'init', args: [supply] }, ...calls]);
  const actual = ['ok', ...logs(chain.receipt), ...calls.flatMap(onChain)];
  expect(actual).toEqual(expected);
  // The sequence must reach the paths that matter.
  const text = expected.join('\n');
  expect(text).toMatch(/revert/);
  expect(text).toMatch(new RegExp(`Approval\\S* \\d+ \\d+ \\| ${limit - 1n}`));
  expect(text).toMatch(/log Transfer\S* [1-9]\d* \d+ \| [1-9]/);
}, 300_000);

test('the constructor reverts without its argument', () => {
  const create = code => chain.cast('send', '--unlocked', '--from', address(people[0]), '--create', code);
  const code = '0x' + chain.bytecode;
  expect(create(code).ok).toBe(false);
  expect(create(code + '00'.repeat(31)).ok).toBe(false);
  expect(create(code + '00'.repeat(32)).ok).toBe(true);
});
