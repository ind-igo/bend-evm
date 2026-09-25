import { afterAll, beforeAll, expect, test } from 'bun:test';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { entries, spawn, top } from '../scripts/tools.js';
import { deploy, must, reverts, run } from './chain.js';
import { keys, separator, sign } from './permit.js';

const bob = '0x0000000000000000000000000000000000000b0b';
const carol = '0x0000000000000000000000000000000000000ca1';
const topic = must(run('cast', 'keccak', 'Transfer(address,address,uint256)'));
const approval = must(run('cast', 'keccak', 'Approval(address,address,uint256)'));
const ownership = must(run('cast', 'keccak', 'OwnershipTransferred(address,address)'));
const word = x => '0x' + BigInt(x).toString(16).padStart(64, '0');
const out = path.join(mkdtempSync(path.join(tmpdir(), 'bend-evm-token-')), 'Token');
let chain, sender, send, owner;

// As a user would: bun run build --out, then deploy the bytecode with no
// initial supply. The deployer, sender, is the owner. The build writes
// CERT.bend, which must equal the committed one; the committed copy goes
// back either way.
const cert = 'examples/token/CERT.bend';
const committed = readFileSync(cert, 'utf8');
let built;

beforeAll(async () => {
  try {
    must(spawn([process.execPath, 'scripts/build.js', '--out', out, 'examples/token/program.bend', ...entries.token],
      { timeout: 600_000 }));
  } finally {
    built = readFileSync(cert, 'utf8');
    writeFileSync(cert, committed);
  }
  chain = await deploy({ bytecode: readFileSync(out + '.bin', 'utf8').trim(), args: [0n] });
  ({ sender, send } = chain);
  owner = sender;
  for (const who of [bob, carol]) chain.fund(who);
}, 600_000);

afterAll(() => {
  rmSync(path.dirname(out), { recursive: true, force: true });
  return chain?.stop();
});

test('the committed certificate is current', () => {
  expect(built).toBe(committed);
});

test('wallets read the name, symbol and decimals, and the ABI is valid', () => {
  expect(must(chain.cast('call', chain.address, 'name()(string)'))).toBe('"Bend Token"');
  expect(must(chain.cast('call', chain.address, 'symbol()(string)'))).toBe('"BEND"');
  expect(must(chain.cast('call', chain.address, 'decimals()(uint8)'))).toBe('18');
  const solidity = must(run('cast', 'interface', out + '.abi.json'));
  for (const line of ['function transfer(address to, uint256 amount) external returns (bool);',
    'function owner() external view returns (address);', 'function name() external pure returns (string memory);',
    'event Transfer(address indexed, address indexed, uint256);']) {
    expect(solidity).toContain(line);
  }
});

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
  const before = supply();
  must(chain.cast('rpc', 'anvil_setStorageAt', chain.address, '0x0', word(top)));
  reverts(send(owner, 'mint(address,uint256)', bob, '1'));
  must(chain.cast('rpc', 'anvil_setStorageAt', chain.address, '0x0', word(before)));
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
  must(send(sender, 'approve(address,uint256)', bob, String(top)));
  must(send(bob, 'transferFrom(address,address,uint256)', sender, carol, '10'));
  expect(allowance(sender, bob)).toBe(top);
  expect(balance(sender)).toBe(40n);
  expect(balance(carol)).toBe(30n);
  must(send(sender, 'approve(address,uint256)', bob, String(top - 1n)));
  must(send(bob, 'transferFrom(address,address,uint256)', sender, carol, '10'));
  expect(allowance(sender, bob)).toBe(top - 11n);
});

test('a holder burns its own tokens, and burn logs a Transfer to zero', () => {
  const before = balance(bob);
  const total = supply();
  reverts(send(bob, 'burn(uint256)', String(before + 1n)));
  const [topics, data] = logged(send(bob, '--json', 'burn(uint256)', '1'));
  expect(topics).toEqual([topic, word(bob), word(0)]);
  expect(data).toBe(word(1));
  expect(balance(bob)).toBe(before - 1n);
  expect(supply()).toBe(total - 1n);
});

test('a permit signed by the owner sets the allowance once, before its deadline', () => {
  const [holder, other] = Object.keys(keys);
  const domain = must(chain.cast('call', chain.address, 'DOMAIN_SEPARATOR()(bytes32)'));
  const chainId = must(chain.cast('chain-id'));
  expect(domain).toBe(separator('Bend Token', chainId, chain.address));
  const now = Number(must(chain.cast('block', 'latest', '--field', 'timestamp')));
  const permit = (signer, owner, value, deadline, nonce = 0) =>
    [owner, bob, String(value), String(deadline), ...sign(keys[signer], domain, owner, bob, value, nonce, deadline)];
  const call = args => send(carol, '--json', 'permit(address,address,uint256,uint256,uint8,bytes32,bytes32)', ...args);
  const nonce = who => chain.word('nonces(address)(uint256)', who);

  reverts(call(permit(other, holder, 5, now + 1000)));
  reverts(call(permit(holder, holder, 5, now - 1)));
  // ecrecover gives zero for a bad signature, so the zero owner must not pass.
  reverts(call(['0x0000000000000000000000000000000000000000', bob, '5', String(now + 1000), '27',
    '0x' + '11'.repeat(32), '0x' + '22'.repeat(32)]));
  const good = permit(holder, holder, 5, now + 1000);
  const [topics, data] = logged(call(good));
  expect(topics).toEqual([approval, word(holder), word(bob)]);
  expect(data).toBe(word(5));
  expect(allowance(holder, bob)).toBe(5n);
  expect(nonce(holder)).toBe(1n);
  reverts(call(good));
  must(call(permit(holder, holder, 7, now + 1000, 1)));
  expect(allowance(holder, bob)).toBe(7n);
});
