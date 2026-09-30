import { expect, test } from 'bun:test';
import { bend, entries } from '../scripts/tools.js';
import { arity, evm, words } from './evm.js';
import { deploy, must, run } from './chain.js';
import { generator } from './random.js';

// The model's word operations (Evm.op) against the reference in evm.js. The
// Bend runtime holds words below 2^48, so the model runs at 24 bits, where a
// product still fits. The width comes from the limit, so this is the same
// code that runs at 256 bits in a proof. SEED=<n> runs other words.
const seed = Number(process.env.SEED ?? 1);
const w = 24;

test(`the model's word operations agree with the reference at ${w} bits (SEED=${seed})`, () => {
  const random = generator(seed);
  const pick = xs => xs[Math.floor(random() * xs.length)];
  const ws = words(w, random, 16);
  for (const op of Object.keys(arity)) {
    const cases = arity[op] === 1 ? ws.map(a => [a])
      : arity[op] === 2 ? ws.flatMap(a => ws.map(b => [a, b]))
      : Array.from({ length: 600 }, () => [pick(ws), pick(ws), pick(ws)]);
    const out = must(bend('tests/fixtures/model/math.bend', String(1n << BigInt(w)),
      ...cases.flatMap(args => [...args.map(String), op]))).trim().split('\n');
    const wrong = cases.map((args, i) => [args, out[i], String(evm(op, args, w))]).filter(([, got, want]) => got !== want);
    expect({ op, wrong: wrong.slice(0, 5) }).toEqual({ op, wrong: [] });
  }
}, 300_000);

// The floor of the square root, by bisection.
function isqrt(x) {
  let lo = 0n, hi = 1n << 128n;
  while (hi - lo > 1n) {
    const mid = (lo + hi) / 2n;
    if (mid * mid <= x) lo = mid; else hi = mid;
  }
  return lo;
}

// Words for sqrt: the edge and random words, squares, and the words next to
// them, where Newton's method ends one above the root.
const roots = ws => [...ws, ...[0n, 1n, 2n, 3n, 4n, 1n << 128n, (1n << 128n) - 1n, (1n << 64n) + 7n, 1n << 136n, 1n << 72n,
  1n << 40n, 1n << 24n].flatMap(r => [r * r - 1n, r * r, r * r + 1n].filter(x => x >= 0n && x < 1n << 256n))].map(a => [a]);

// The compiled operations on anvil against the reference at 256 bits. This
// tests the printer and the Yul fragment's meaning for each operation, which
// the proofs take as given. Checked mul reverts on overflow, and checked div
// and mod on zero. The AMM's sqrt is checked here too.
test(`the compiled word operations agree with the reference on anvil (SEED=${seed})`, async () => {
  const chain = await deploy({ program: 'tests/fixtures/math/program.bend', functions: entries.math });
  try {
    const random = generator(seed);
    const pick = xs => xs[Math.floor(random() * xs.length)];
    const ws = words(256, random, 8);
    const checked = { checked_mul: 'mul', checked_div: 'div', checked_mod: 'mod' };
    // The signed entries take Evm.Int, int256 in the ABI; the words are the same.
    const types = { sdiv: ['int256', 'int256'], smod: ['int256', 'int256'], slt: ['int256', 'int256'],
      sgt: ['int256', 'int256'], sar: ['uint256', 'int256'] };
    const want = (f, args) => {
      if (f === 'sqrt') return String(isqrt(args[0]));
      if (!checked[f]) return String(evm(f, args));
      const [a, b] = args;
      if (f === 'checked_mul' ? a * b >= 1n << 256n : b === 0n) return 'revert';
      return String(evm(checked[f], args));
    };
    for (const f of entries.math) {
      const n = f === 'sqrt' ? 1 : arity[f] ?? 2;
      const cases = f === 'sqrt' ? roots(ws) : n === 1 ? ws.map(a => [a]) : n === 2 ? ws.flatMap(a => ws.map(b => [a, b]))
        : Array.from({ length: 300 }, () => [pick(ws), pick(ws), pick(ws)]);
      const selector = must(run('cast', 'sig', `${f}(${(types[f] ?? Array(n).fill('uint256')).join(',')})`));
      const body = cases.map((args, id) => ({ jsonrpc: '2.0', id, method: 'eth_call', params: [{ to: chain.address,
        data: selector + args.map(x => x.toString(16).padStart(64, '0')).join('') }, 'latest'] }));
      const replies = await (await fetch(chain.rpc, { method: 'POST', headers: { 'content-type': 'application/json' },
        body: JSON.stringify(body) })).json();
      const got = new Map(replies.map(r => [r.id, r.error ? 'revert' : String(BigInt(r.result))]));
      const wrong = cases.map((args, i) => [args.map(String), got.get(i), want(f, args)]).filter(([, g, w]) => g !== w);
      expect({ f, wrong: wrong.slice(0, 5) }).toEqual({ f, wrong: [] });
    }
  } finally {
    await chain.stop();
  }
}, 300_000);
