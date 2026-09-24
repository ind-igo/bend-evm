import { afterAll, beforeAll, expect, test } from 'bun:test';
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

// Compiles the Counter to Yul, deploys it on a local anvil chain with real
// transactions, and calls it through the standard ABI with cast.
const root = path.resolve(import.meta.dir, '..');
const temp = mkdtempSync(path.join(tmpdir(), 'bend-evm-counter-'));
const owner = '0x0000000000000000000000000000000000000007';
const max = '0x' + 'f'.repeat(64);
let node, rpc, sender, address;

function run(command, ...args) {
  const child = Bun.spawnSync([command, ...args], { cwd: root, timeout: 120_000 });
  return { ok: child.exitCode === 0, out: child.stdout.toString().trim(), err: child.stderr.toString() };
}

function must(result) {
  if (!result.ok) throw new Error(result.err);
  return result.out;
}

// A failed command must be a revert, not a cast usage error.
function reverts(result) {
  expect(result.ok).toBe(false);
  expect(result.err).toMatch(/revert/i);
}

const cast = (command, ...args) => run('cast', command, '--rpc-url', rpc, ...args);
const send = (from, ...args) => cast('send', '--unlocked', '--from', from, address, ...args);
const get = () => BigInt(must(cast('call', address, 'get()(uint256)')).split(' ')[0]);

beforeAll(async () => {
  const yul = must(run(process.execPath, 'vendor/bend-frontend/host/run.js', 'src/compile.bend',
    'examples/counter/program.bend', 'get', 'increment', 'set'));
  writeFileSync(path.join(temp, 'Counter.yul'), yul);
  const solc = must(run('solc', '--strict-assembly', '--evm-version', 'shanghai', '--bin', path.join(temp, 'Counter.yul')));
  const bytecode = solc.split('Binary representation:')[1].trim();

  node = Bun.spawn(['anvil', '--host', '127.0.0.1', '--port', '0'], { stdout: 'pipe', stderr: 'pipe' });
  const reader = node.stdout.getReader();
  let output = '';
  while (!rpc) {
    const chunk = await reader.read();
    if (chunk.done) throw new Error('anvil stopped before it listened');
    output += new TextDecoder().decode(chunk.value);
    const port = output.match(/Listening on 127\.0\.0\.1:(\d+)/)?.[1];
    if (port) rpc = `http://127.0.0.1:${port}`;
  }
  reader.releaseLock();
  sender = must(cast('rpc', 'eth_accounts')).match(/0x[0-9a-fA-F]{40}/)[0];
  const receipt = JSON.parse(must(cast('send', '--unlocked', '--from', sender, '--json', '--create', '0x' + bytecode)));
  address = receipt.contractAddress;
  must(cast('rpc', 'anvil_impersonateAccount', owner));
  must(cast('rpc', 'anvil_setBalance', owner, '0x56bc75e2d63100000'));
}, 120_000);

afterAll(async () => {
  node?.kill();
  await node?.exited;
  rmSync(temp, { recursive: true, force: true });
});

test('get and increment', () => {
  expect(get()).toBe(0n);
  must(send(sender, 'increment()'));
  must(send(sender, 'increment()'));
  expect(get()).toBe(2n);
});

test('only the owner can set', () => {
  must(send(owner, 'set(uint256)', '42'));
  expect(get()).toBe(42n);
  reverts(send(sender, 'set(uint256)', '7'));
  expect(get()).toBe(42n);
});

test('increment reverts on overflow', () => {
  must(cast('rpc', 'anvil_setStorageAt', address, '0x0', max));
  reverts(send(sender, 'increment()'));
  expect(get()).toBe(2n ** 256n - 1n);
  must(send(owner, 'set(uint256)', '0'));
});

test('rejects ETH, unknown selectors and short calldata', () => {
  reverts(send(sender, 'increment()', '--value', '1'));
  reverts(cast('call', address, 'decrement()'));
  reverts(cast('call', '--from', owner, address, '0x60fe47b1'));
  expect(get()).toBe(0n);
});
