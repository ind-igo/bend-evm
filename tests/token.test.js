import { afterAll, beforeAll, expect, test } from 'bun:test';
import { deploy, must, reverts, run } from './chain.js';

const bob = '0x0000000000000000000000000000000000000b0b';
const carol = '0x0000000000000000000000000000000000000ca1';
const topic = must(run('cast', 'keccak', 'Transfer(address,address,uint256)'));
const approval = must(run('cast', 'keccak', 'Approval(address,address,uint256)'));
const ownership = must(run('cast', 'keccak', 'OwnershipTransferred(address,address)'));
const word = x => '0x' + BigInt(x).toString(16).padStart(64, '0');
let chain, sender, send, owner;

// The deployer, sender, is the owner.
beforeAll(async () => {
  chain = await deploy('examples/token/program.bend', ['init', 'owner', 'transferOwnership', 'totalSupply', 'balanceOf',
    'transfer', 'mint', 'allowance', 'approve', 'transferFrom'], undefined, [0n]);
  ({ sender, send } = chain);
  owner = sender;
  for (const who of [bob, carol]) {
    must(chain.cast('rpc', 'anvil_impersonateAccount', who));
    must(chain.cast('rpc', 'anvil_setBalance', who, '0x56bc75e2d63100000'));
  }
}, 120_000);

afterAll(() => chain?.stop());

const supply = () => chain.word('totalSupply()(uint256)');
const balance = who => chain.word('balanceOf(address)(uint256)', who);
const allowance = (holder, spender) => chain.word('allowance(address,address)(uint256)', holder, spender);

// The one log of a transaction, as [topics, data].
function logged(result) {
  const logs = JSON.parse(must(result)).logs;
  expect(logs.length).toBe(1);
  return [logs[0].topics, logs[0].data];
}

test('the deployer owns the token and can hand ownership on', () => {
  expect(chain.word('owner()(address)')).toBe(BigInt(sender));
  reverts(send(bob, 'transferOwnership(address)', bob));
  const [topics, data] = logged(send(sender, '--json', 'transferOwnership(address)', bob));
  expect(topics).toEqual([ownership, word(sender), word(bob)]);
  expect(data).toBe('0x');
  expect(chain.word('owner()(address)')).toBe(BigInt(bob));
  reverts(send(sender, 'transferOwnership(address)', sender));
  must(send(bob, 'transferOwnership(address)', sender));
});

test('the owner mints, and mint logs a Transfer from zero', () => {
  const [topics, data] = logged(send(owner, '--json', 'mint(address,uint256)', sender, '100'));
  expect(topics).toEqual([topic, word(0), word(sender)]);
  expect(data).toBe(word(100));
  expect(supply()).toBe(100n);
  expect(balance(sender)).toBe(100n);
  reverts(send(bob, 'mint(address,uint256)', sender, '1'));
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

test('approve sets the allowance at the nested Solidity layout and logs Approval', () => {
  const [topics, data] = logged(send(sender, '--json', 'approve(address,uint256)', bob, '50'));
  expect(topics).toEqual([approval, word(sender), word(bob)]);
  expect(data).toBe(word(50));
  expect(allowance(sender, bob)).toBe(50n);
  expect(allowance(bob, sender)).toBe(0n);
  const inner = must(run('cast', 'index', 'address', sender, '2'));
  const slot = must(run('cast', 'index', 'address', bob, inner));
  expect(BigInt(must(chain.cast('storage', chain.address, slot)))).toBe(50n);
});

test('transferFrom spends the allowance and moves the amount', () => {
  const [topics, data] = logged(send(bob, '--json', 'transferFrom(address,address,uint256)', sender, carol, '20'));
  expect(topics).toEqual([topic, word(sender), word(carol)]);
  expect(data).toBe(word(20));
  expect(allowance(sender, bob)).toBe(30n);
  expect(balance(sender)).toBe(50n);
  expect(balance(carol)).toBe(20n);
  expect(supply()).toBe(100n);
});

test('transferFrom reverts above the allowance or the balance', () => {
  reverts(send(bob, 'transferFrom(address,address,uint256)', sender, carol, '31'));
  reverts(send(carol, 'transferFrom(address,address,uint256)', sender, carol, '1'));
  must(send(sender, 'approve(address,uint256)', bob, '1000'));
  reverts(send(bob, 'transferFrom(address,address,uint256)', sender, carol, '51'));
  expect(allowance(sender, bob)).toBe(1000n);
  expect(balance(sender)).toBe(50n);
});

test('an allowance of max is unlimited', () => {
  const max = (2n ** 256n - 1n).toString();
  must(send(sender, 'approve(address,uint256)', bob, max));
  must(send(bob, 'transferFrom(address,address,uint256)', sender, carol, '10'));
  expect(allowance(sender, bob)).toBe(2n ** 256n - 1n);
  expect(balance(sender)).toBe(40n);
  expect(balance(carol)).toBe(30n);
  must(send(sender, 'approve(address,uint256)', bob, (2n ** 256n - 2n).toString()));
  must(send(bob, 'transferFrom(address,address,uint256)', sender, carol, '10'));
  expect(allowance(sender, bob)).toBe(2n ** 256n - 12n);
});
