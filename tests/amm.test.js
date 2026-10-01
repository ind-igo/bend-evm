import { afterAll, beforeAll, expect, test } from 'bun:test';
import { bend, bytecode, entries, top } from '../scripts/tools.js';
import { deploy, must, run } from './chain.js';
import { generator } from './random.js';

// A differential test against Solidity. The Bend pair (examples/amm) and
// the same pair in Solidity (tests/fixtures/reference/Pair.sol) each get two
// Coins, which can misbehave or call back into the pair when it pays, and
// share a Borrower for flash swaps, which pays back or not, and can flash
// swap again inside its call. Both
// get the same random steps on one anvil chain, and must give the same
// results, revert data, logs and state after each step. Addresses become
// names first, as the two sides have their own. Solidity's arithmetic
// reverts with Panic(0x11) and the Bend pair with no data, so only 4-byte
// custom errors are compared. SEED=<n> runs another sequence.
const seed = Number(process.env.SEED ?? 1);
const solidity = must(run('solc', '--evm-version', 'cancun', '--bin', 'tests/fixtures/reference/Pair.sol'));
const code = name => solidity.split(`:${name} =======`)[1].split('Binary:')[1].trim().split('\n')[0];
let chain, people, sides, names, borrower;

const create = (from, bytecode, args = '') =>
  JSON.parse(must(chain.cast('send', '--unlocked', '--from', from, '--json', '--create', '0x' + bytecode + args))).contractAddress;
const encode = (...addresses) => addresses.map(a => a.slice(2).toLowerCase().padStart(64, '0')).join('');

beforeAll(async () => {
  chain = await deploy({ bytecode: code('Coin') });
  people = must(chain.cast('rpc', 'eth_accounts')).match(/0x[0-9a-fA-F]{40}/g).slice(0, 3);
  const coins = [chain.address, create(people[0], code('Coin')), create(people[0], code('Coin')), create(people[0], code('Coin'))];
  const ours = create(people[0], bytecode(must(bend('src/compile.bend', 'examples/amm/Pair.bend', ...entries.amm))),
    encode(coins[0], coins[1]));
  const sol = create(people[0], code('Pair'), encode(coins[2], coins[3]));
  borrower = create(people[0], code('Borrower'));
  sides = [{ pair: ours, coins: coins.slice(0, 2) }, { pair: sol, coins: coins.slice(2) }];
  names = new Map([[ours, 'pair'], [sol, 'pair'], [coins[0], 'coin0'], [coins[2], 'coin0'], [coins[1], 'coin1'],
    [coins[3], 'coin1'], [borrower, 'borrower'], ...people.map((p, i) => [p, `person${i}`])].map(([a, n]) => [a.slice(2).toLowerCase(), n]));
}, 120_000);

afterAll(() => chain?.stop());

const named = text => [...names].reduce((t, [a, n]) => t.replaceAll(a, n), text.toLowerCase());

// What one transaction did: "ok <returndata> <logs>" or "revert <error>".
function effect(from, to, signature, ...args) {
  const call = chain.cast('call', '--from', from, to, signature, ...args);
  if (!call.ok) {
    expect(call.err).toMatch(/revert/i);
    const data = call.err.match(/data: "0x([0-9a-f]*)"/)?.[1] ?? '';
    return `revert ${data.length === 8 ? data : ''}`;
  }
  const receipt = JSON.parse(must(chain.cast('send', '--unlocked', '--from', from, '--json', to, signature, ...args)));
  expect(receipt.status).toBe('0x1');
  return named(['ok', call.out, ...receipt.logs.map(l => `${l.address} ${l.topics.join(' ')} ${l.data}`)].join(' '));
}

const word = (to, signature, ...args) => BigInt(must(chain.cast('call', to, signature, ...args)).split(' ')[0]);

function state({ pair, coins }) {
  const lp = [...people, pair, '0x0000000000000000000000000000000000000000'].map(p => word(pair, 'balanceOf(address)(uint256)', p));
  const reserves = must(chain.cast('call', pair, 'getReserves()(uint256,uint256)')).split('\n').map(l => l.split(' ')[0]);
  return ['state', ...reserves, word(pair, 'totalSupply()(uint256)'),
    ...lp, ...coins.map(c => word(c, 'balanceOf(address)(uint256)', pair))].join(' ');
}

// The amount out for amount in, as Uniswap's getAmountOut computes it.
const out = (amount, rIn, rOut) => rIn === 0n ? 0n : amount * 997n * rOut / (rIn * 1000n + amount * 997n);

function steps(random, length) {
  const pick = xs => xs[Math.floor(random() * xs.length)];
  const small = () => BigInt(Math.floor(random() * 5000));
  const amount = () => random() < 0.8 ? small() * pick([1n, 1000n, 10n ** 18n])
    : pick([1n << 128n, 1n << 200n, top - small(), small()]);
  const list = [];
  for (let i = 0; i < length; i++) {
    const who = pick(people);
    list.push(pick([
      { kind: 'fund', coin: pick([0, 1]), amount: amount() },
      { kind: 'fund', coin: pick([0, 1]), amount: amount() },
      { kind: 'add', a0: amount(), a1: amount(), who },
      { kind: 'add', a0: amount(), a1: amount(), who },
      { kind: 'mint', who },
      { kind: 'remove', part: random(), who },
      { kind: 'burn', who },
      { kind: 'swap', coin: pick([0, 1]), amount: amount(), extra: pick([0n, 0n, 0n, 1n, -1n]), who },
      { kind: 'swap', coin: pick([0, 1]), amount: amount(), extra: 0n, who },
      { kind: 'swap', coin: pick([0, 1]), amount: amount(), extra: 0n, who },
      { kind: 'raw', a0: amount(), a1: amount(), to: pick([...people, 'coin0', 'coin1']), who },
      { kind: 'flash', coin: pick([0, 1]), amount: amount(), extra: pick([0n, 0n, 1n, -1n]), mode: pick([0, 0, 1, 2]), who },
      { kind: 'sync', who },
      { kind: 'mode', coin: pick([0, 1]), mode: pick([0, 0, 0, 1, 2, 3, 4, 4, 5, 5]) },
    ]));
  }
  return list;
}

// Steps that reach the paths that matter, before the random ones: a swap
// that asks one token too many, a token that returns false, and tokens that
// call back into the pair while it pays.
function scripted() {
  const [a, b] = people;
  const swap = (coin, extra = 0n) => ({ kind: 'swap', coin, amount: 10n ** 18n, extra, who: b });
  const mode = (coin, m) => ({ kind: 'mode', coin, mode: m });
  return [
    { kind: 'add', a0: 10n ** 21n, a1: 4n * 10n ** 21n, who: a },
    swap(0, 1n), swap(0), swap(1, 1n), swap(1),
    mode(1, 1), swap(0), mode(1, 2), swap(0), mode(1, 0),
    mode(0, 3), swap(1), mode(0, 4), swap(1), swap(0), mode(0, 5), swap(1), mode(0, 0),
    { kind: 'add', a0: 10n ** 18n, a1: 10n ** 18n, who: b },
    { kind: 'remove', part: 0.5, who: a },
    mode(1, 4), { kind: 'remove', part: 0.5, who: b }, mode(1, 0),
    ...[0n, -1n].flatMap(extra => [0, 1, 2].map(m => ({ kind: 'flash', coin: 0, amount: 10n ** 18n, extra, mode: m, who: b }))),
    // A flash swap to an account with no code reverts before the call.
    { kind: 'raw', a0: 1n, a1: 0n, to: a, data: '0x01', who: b },
  ];
}

// One step on one side, as lines of text.
function apply(side, step) {
  const { pair, coins } = side;
  const fund = (c, amount) => effect(people[0], coins[c], 'mint(address,uint256)', pair, String(amount));
  const r = () => [word(pair, 'reserve0()(uint256)'), word(pair, 'reserve1()(uint256)')];
  switch (step.kind) {
    case 'fund':
      return [fund(step.coin, step.amount)];
    case 'add':
      return [fund(0, step.a0), fund(1, step.a1), effect(step.who, pair, 'mint(address)', step.who)];
    case 'mint':
      return [effect(step.who, pair, 'mint(address)', step.who)];
    case 'remove': {
      const held = word(pair, 'balanceOf(address)(uint256)', step.who);
      const part = BigInt(Math.floor(step.part * 1000)) * held / 1000n;
      return [effect(step.who, pair, 'transfer(address,uint256)', pair, String(part)), effect(step.who, pair, 'burn(address)', step.who)];
    }
    case 'burn':
      return [effect(step.who, pair, 'burn(address)', step.who)];
    case 'swap': {
      const [r0, r1] = r();
      const [rIn, rOut] = step.coin === 0 ? [r0, r1] : [r1, r0];
      const o = out(step.amount, rIn, rOut) + step.extra;
      const outs = step.coin === 0 ? ['0', String(o < 0n ? 0n : o)] : [String(o < 0n ? 0n : o), '0'];
      return [fund(step.coin, step.amount), effect(step.who, pair, 'swap(uint256,uint256,address,bytes)', ...outs, step.who, '0x')];
    }
    case 'raw': {
      const to = step.to === 'coin0' ? coins[0] : step.to === 'coin1' ? coins[1] : step.to;
      return [effect(step.who, pair, 'swap(uint256,uint256,address,bytes)', String(step.a0), String(step.a1), to, step.data ?? '0x')];
    }
    case 'flash': {
      // Out of one coin, paid back in the same coin: the amount less the
      // fee, rounded up, is enough; one less is not.
      const [r0, r1] = r();
      const o = step.amount < (step.coin === 0 ? r0 : r1) ? step.amount : 1n;
      const paid = o * 1000n / 997n + 1n + step.extra;
      const pays = step.coin === 0 ? [paid, 0n] : [0n, paid];
      const outs = step.coin === 0 ? [o, 0n] : [0n, o];
      const data = must(run('cast', 'abi-encode', 'f(uint256,uint256,uint256)', ...pays.map(String), String(step.mode)));
      return [effect(step.who, pair, 'swap(uint256,uint256,address,bytes)', ...outs.map(String), borrower, data)];
    }
    case 'sync':
      return [effect(step.who, pair, 'sync()')];
    case 'mode':
      return [effect(people[0], coins[step.coin], 'setMode(uint256)', String(step.mode))];
  }
}

test(`the Bend pair and the Solidity pair agree on random steps (SEED=${seed})`, () => {
  const list = [...scripted(), ...steps(generator(seed), 100)];
  const lines = sides.map(() => []);
  for (const step of list) {
    const text = JSON.stringify(step, (_, v) => typeof v === 'bigint' ? String(v) : v);
    sides.forEach((side, i) => lines[i].push(text, ...apply(side, step), state(side)));
  }
  expect(lines[0]).toEqual(lines[1]);
  if (process.env.DUMP) Bun.write(process.env.DUMP, lines[0].join("\n"));
  // The steps must reach the paths that matter: flash swaps that pay back
  // and pass, and ones that do not.
  const all = lines[0].join('\n');
  const flashes = lines[0].map((l, i) => [l, lines[0][i + 1]]).filter(([l]) => l.includes('"flash"'));
  expect(flashes.filter(([, r]) => r.startsWith('ok')).length).toBeGreaterThan(2);
  expect(flashes.filter(([, r]) => r.startsWith('revert')).length).toBeGreaterThan(2);
  for (const error of ['K()', 'InsufficientInputAmount()', 'InsufficientLiquidity()', 'TransferFailed()', 'InvalidTo()',
    'InsufficientLiquidityMinted()', 'InsufficientLiquidityBurned()']) {
    expect(all).toContain(`revert ${must(run('cast', 'sig', error)).slice(2)}`);
  }
  for (const event of ['Swap(address,address,uint256,uint256,uint256,uint256)', 'Burn(address,address,uint256,uint256)',
    'Mint(address,uint256,uint256)']) {
    expect(all.split(must(run('cast', 'keccak', event))).length).toBeGreaterThan(3);
  }
}, 600_000);
