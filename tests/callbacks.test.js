import { afterAll, beforeAll, expect, test } from 'bun:test';
import { bend, bytecode, entries } from '../scripts/tools.js';
import { deploy, must, run } from './chain.js';
import { generator } from './random.js';

// A differential test of the model of calls and callbacks (calls.bend):
// random transactions to the vault on anvil, over the token in Hook.sol,
// which calls back in many ways. anvil's call trace of each transaction
// gives its answers and callbacks, and the vault's certified entries run
// with them in Bend (tests/fixtures/model/vault.bend). Both must give the
// same result and the same shares after each transaction. This tests what
// the proofs take as given: that the model of callbacks, reverts and the
// caller matches the EVM, and that the entry table matches the dispatcher.
// SEED=<n> runs another sequence.
const seed = Number(process.env.SEED ?? 1);
const limit = 1n << 40n;
const program = 'tests/fixtures/vault/program.bend';
const functions = ['token()', 'sharesOf(address)', 'totalShares()', 'deposit(uint256)', 'withdraw(uint256)',
  'ping(uint256)', 'touch(uint256)'];
const hooks = ['transfer(address,uint256)', 'transferFrom(address,address,uint256)', 'ping(uint256)'];
const selector = f => must(run('cast', 'sig', f));
const table = new Map(functions.map((f, i) => [selector(f), i]));
const names = new Map(hooks.map(f => [selector(f), f.split('(')[0]]));
let chain, vault, people, ids;

// An address as the model's small account number; other words as they are.
const word = hex => {
  const x = BigInt('0x' + hex);
  return String(ids.get(x) ?? x);
};
const args = input => (input.slice(10).match(/.{64}/g) ?? []).map(word);
const id = address => String(ids.get(BigInt(address)));

// A frame of a call into the vault, as an Enter: its answers are the calls
// that it makes. A call that reverts or gives no word has no answer, so the
// model reverts there, as the vault does.
function enter(frame) {
  const answers = [];
  for (const call of frame.calls ?? []) {
    if (call.error || (call.output ?? '0x').length < 66) break;
    const callbacks = (call.calls ?? []).filter(c => BigInt(c.to) === BigInt(vault)).flatMap(enter);
    answers.push(id(call.to), names.get(call.input.slice(0, 10)), '[', ...args(call.input), ']w',
      '[', ...callbacks, ']s', word(call.output.slice(2, 66)), 'A');
  }
  const entry = table.get(frame.input.slice(0, 10));
  expect(entry).toBeDefined();
  return [id(frame.from), String(entry), '[', ...args(frame.input), ']w', '[', ...answers, ']s', 'E'];
}

const slot = n => BigInt(must(chain.cast('storage', vault, String(n))));
const shares = who => BigInt(must(chain.cast('call', vault, 'sharesOf(address)(uint256)', who)).split(' ')[0]);
const line = ok => [ok ? 'ok' : 'revert', ...[...people.values()].map(shares),
  BigInt(must(chain.cast('call', vault, 'totalShares()(uint256)')).split(' ')[0]), ids.get(slot(3)) ?? slot(3)].join(' ');

beforeAll(async () => {
  const solidity = must(run('solc', '--evm-version', 'cancun', '--bin', 'tests/fixtures/vault/Hook.sol'));
  chain = await deploy({ bytecode: solidity.split('Binary:')[1].trim().split('\n')[0] });
  const code = bytecode(must(bend('src/compile.bend', program, ...entries.vault)));
  vault = JSON.parse(must(chain.cast('send', '--unlocked', '--from', chain.sender, '--json', '--create',
    '0x' + code + chain.address.slice(2).padStart(64, '0')))).contractAddress;
  const other = must(chain.cast('rpc', 'eth_accounts')).match(/0x[0-9a-fA-F]{40}/g)[1];
  // The accounts 1 to 4 of the model: two senders, the token and the vault.
  people = new Map([[1, chain.sender], [2, chain.address], [3, vault], [4, other]]);
  ids = new Map([...people].map(([n, a]) => [BigInt(a), n]));
  for (const who of [chain.sender, other, chain.address]) must(chain.send(chain.sender, 'mint(address,uint256)', who, '1000'));
}, 120_000);

afterAll(() => chain?.stop());

test(`the model of callbacks agrees with anvil on random transactions (SEED=${seed})`, () => {
  const random = generator(seed);
  const pick = xs => xs[Math.floor(random() * xs.length)];
  const tokens = [], expected = [];
  for (let i = 0; i < 100; i++) {
    must(chain.send(chain.sender, 'setMode(uint256)', String(pick([0, 1, 1, 2, 2, 3, 4, 5, 6, 6, 7, 7, 7]))));
    const f = pick(['deposit(uint256)', 'deposit(uint256)', 'deposit(uint256)', 'withdraw(uint256)', 'withdraw(uint256)',
      'withdraw(uint256)', 'ping(uint256)', 'touch(uint256)', 'touch(uint256)', 'totalShares()', 'sharesOf(address)']);
    const arg = f === 'sharesOf(address)' ? [people.get(pick([1, 2, 4]))] : f.endsWith('()') ? [] : [String(Math.floor(random() * 12))];
    // A fixed gas limit mines a transaction that reverts, so it has a trace.
    const receipt = JSON.parse(must(chain.cast('send', '--unlocked', '--from', people.get(pick([1, 4])), '--json',
      '--gas-limit', '3000000', vault, f, ...arg)));
    const trace = JSON.parse(must(chain.cast('rpc', 'debug_traceTransaction', receipt.transactionHash, '{"tracer":"callTracer"}')));
    tokens.push(...enter(trace), 'T');
    expected.push(line(receipt.status === '0x1'));
  }
  const actual = must(bend('tests/fixtures/model/vault.bend', String(limit), ...tokens)).split('\n');
  expect(actual).toEqual(expected);
  // The sequence must reach the paths that matter: entries that revert,
  // and callbacks into deposit, withdraw and a view, from the token.
  expect(expected.filter(l => l.startsWith('revert')).length).toBeGreaterThan(5);
  const text = tokens.join(' ');
  for (const entry of [2, 3, 4]) expect(text).toContain(`[ 2 ${entry} [`);
}, 300_000);
