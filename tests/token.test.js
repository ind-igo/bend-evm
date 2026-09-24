import { afterAll, beforeAll, expect, test } from 'bun:test';
import { deploy, must, owner, reverts, run } from './chain.js';

const bob = '0x0000000000000000000000000000000000000b0b';
const topic = must(run('cast', 'keccak', 'Transfer(address,address,uint256)'));
const word = x => '0x' + BigInt(x).toString(16).padStart(64, '0');
let chain, sender, send;

beforeAll(async () => {
  chain = await deploy('examples/token/program.bend', ['totalSupply', 'balanceOf', 'transfer', 'mint']);
  ({ sender, send } = chain);
}, 120_000);

afterAll(() => chain?.stop());

const supply = () => chain.word('totalSupply()(uint256)');
const balance = who => chain.word('balanceOf(address)(uint256)', who);

// The one log of a transaction, as [topics, data].
function logged(result) {
  const logs = JSON.parse(must(result)).logs;
  expect(logs.length).toBe(1);
  return [logs[0].topics, logs[0].data];
}

test('the owner mints, and mint logs a Transfer from zero', () => {
  const [topics, data] = logged(send(owner, '--json', 'mint(address,uint256)', sender, '100'));
  expect(topics).toEqual([topic, word(0), word(sender)]);
  expect(data).toBe(word(100));
  expect(supply()).toBe(100n);
  expect(balance(sender)).toBe(100n);
  reverts(send(sender, 'mint(address,uint256)', sender, '1'));
});

test('transfer moves the amount, returns true and logs it', () => {
  expect(must(chain.cast('call', '--from', sender, chain.address, 'transfer(address,uint256)(bool)', bob, '30'))).toBe('true');
  const [topics, data] = logged(send(sender, '--json', 'transfer(address,uint256)', bob, '30'));
  expect(topics).toEqual([topic, word(sender), word(bob)]);
  expect(data).toBe(word(30));
  expect(balance(sender)).toBe(70n);
  expect(balance(bob)).toBe(30n);
  expect(supply()).toBe(100n);
});

test('balances use the Solidity mapping layout at slot 1', () => {
  const slot = must(run('cast', 'index', 'address', bob, '1'));
  expect(BigInt(must(chain.cast('storage', chain.address, slot)))).toBe(30n);
});

test('transfer reverts above the balance, and to self keeps it', () => {
  reverts(send(sender, 'transfer(address,uint256)', bob, '71'));
  must(send(sender, 'transfer(address,uint256)', sender, '70'));
  expect(balance(sender)).toBe(70n);
});

test('mint reverts when the supply would overflow', () => {
  must(chain.cast('rpc', 'anvil_setStorageAt', chain.address, '0x0', word(2n ** 256n - 1n)));
  reverts(send(owner, 'mint(address,uint256)', bob, '1'));
  must(chain.cast('rpc', 'anvil_setStorageAt', chain.address, '0x0', word(100)));
});

test('an address argument above 160 bits reverts', () => {
  const data = '0x70a08231' + '1' + '0'.repeat(23) + bob.slice(2);
  reverts(chain.cast('call', chain.address, data));
  expect(balance(bob)).toBe(30n);
});
