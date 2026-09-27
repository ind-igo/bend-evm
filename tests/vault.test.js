import { afterAll, beforeAll, expect, test } from 'bun:test';
import { bend, bytecode, entries } from '../scripts/tools.js';
import { deploy, must, reverts, run } from './chain.js';

// Evm.call on a chain: a vault over a Solidity token that can call back
// into the vault (tests/fixtures/vault/Hook.sol).
const program = 'tests/fixtures/vault/program.bend';
let chain, vault;

const send = (...args) => chain.cast('send', '--unlocked', '--from', chain.sender, vault, ...args);
const read = (...args) => BigInt(must(chain.cast('call', vault, ...args)).split(' ')[0]);
const held = who => chain.word('balanceOf(address)(uint256)', who);
const state = () => [read('sharesOf(address)(uint256)', chain.sender), read('sharesOf(address)(uint256)', chain.address),
  read('totalShares()(uint256)'), held(vault)];

beforeAll(async () => {
  const solidity = must(run('solc', '--evm-version', 'shanghai', '--bin', 'tests/fixtures/vault/Hook.sol'));
  chain = await deploy({ bytecode: solidity.split('Binary:')[1].trim().split('\n')[0] });
  const code = bytecode(must(bend('src/compile.bend', program, ...entries.vault)));
  const receipt = must(chain.cast('send', '--unlocked', '--from', chain.sender, '--json', '--create',
    '0x' + code + chain.address.slice(2).padStart(64, '0')));
  vault = JSON.parse(receipt).contractAddress;
  // The hook's own tokens pay for the deposit that it makes in a callback.
  must(chain.send(chain.sender, 'mint(address,uint256)', chain.sender, '1000'));
  must(chain.send(chain.sender, 'mint(address,uint256)', chain.address, '1000'));
}, 120_000);

afterAll(() => chain?.stop());

test('deposit and withdraw call the token', () => {
  expect(read('token()(address)') === BigInt(chain.address)).toBe(true);
  must(send('deposit(uint256)', '10'));
  expect(state()).toEqual([10n, 0n, 10n, 10n]);
  must(send('withdraw(uint256)', '4'));
  expect(state()).toEqual([6n, 0n, 6n, 6n]);
  expect(held(chain.sender)).toBe(994n);
});

test('a callback runs an entry inside the call, on the updated state', () => {
  // transferFrom first deposits half the amount again, from the hook.
  must(chain.send(chain.sender, 'setMode(uint256)', '1'));
  must(send('deposit(uint256)', '10'));
  expect(state()).toEqual([16n, 5n, 21n, 21n]);
});

test('a callback that reverts changes nothing when the callee catches it', () => {
  // The hook's callback deposit gives it shares, then reverts, as its own
  // transferFrom returns false.
  must(chain.send(chain.sender, 'setMode(uint256)', '2'));
  must(send('deposit(uint256)', '2'));
  expect(state()).toEqual([18n, 5n, 23n, 23n]);
});

test('an entry reverts when the call returns a word other than 1', () => {
  must(chain.send(chain.sender, 'setMode(uint256)', '3'));
  reverts(send('deposit(uint256)', '1'));
  reverts(send('withdraw(uint256)', '1'));
  expect(state()).toEqual([18n, 5n, 23n, 23n]);
});

test('an entry reverts when the call reverts or returns no data', () => {
  for (const mode of ['4', '5']) {
    must(chain.send(chain.sender, 'setMode(uint256)', mode));
    reverts(send('deposit(uint256)', '1'));
  }
  expect(state()).toEqual([18n, 5n, 23n, 23n]);
  must(chain.send(chain.sender, 'setMode(uint256)', '3'));
});

test('a call as the last step returns its word', () => {
  // The hook is in mode 3 now, and ping adds the mode.
  expect(read('ping(uint256)(uint256)', '4')).toBe(7n);
});

test('the caller after a call is the caller again', () => {
  // ping reads the vault back, from the hook.
  must(chain.send(chain.sender, 'setMode(uint256)', '6'));
  must(send('touch(uint256)', '0'));
  expect(BigInt(must(chain.cast('storage', vault, '3')))).toBe(BigInt(chain.sender));
});

test('a callback during withdraw runs on the state with the shares taken', () => {
  // transfer first withdraws the amount again, from the hook's shares.
  must(chain.send(chain.sender, 'setMode(uint256)', '7'));
  must(send('withdraw(uint256)', '2'));
  expect(state()).toEqual([16n, 3n, 19n, 19n]);
});

test('a function that makes a call that may write is nonpayable', () => {
  const abi = JSON.parse(must(bend('src/abi.bend', program, ...entries.vault)));
  expect(abi.filter(f => f.type === 'function').map(f => [f.name, f.stateMutability])).toEqual([
    ['token', 'view'], ['sharesOf', 'view'], ['totalShares', 'view'], ['deposit', 'nonpayable'], ['withdraw', 'nonpayable'],
    ['ping', 'nonpayable'], ['touch', 'nonpayable']]);
}, 120_000);
