import { expect } from 'bun:test';
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

// Compiles a contract to Yul, deploys it on a local anvil chain with real
// transactions, and calls it through the standard ABI with cast.
const root = path.resolve(import.meta.dir, '..');
export const owner = '0x0000000000000000000000000000000000000007';

export function run(command, ...args) {
  const child = Bun.spawnSync([command, ...args], { cwd: root, timeout: 120_000 });
  return { ok: child.exitCode === 0, out: child.stdout.toString().trim(), err: child.stderr.toString() };
}

export function must(result) {
  if (!result.ok) throw new Error(result.err);
  return result.out;
}

// A failed command must be a revert, not a cast usage error.
export function reverts(result) {
  expect(result.ok).toBe(false);
  expect(result.err).toMatch(/revert/i);
}

// Options: the deployer (anvil's first account by default), the constructor
// arguments, which are words after the code, and bytecode from `bun run
// build --out` (compiled here when absent).
export async function deploy(program, functions, { deployer, args = [], bytecode } = {}) {
  const temp = mkdtempSync(path.join(tmpdir(), 'bend-evm-chain-'));
  if (!bytecode) {
    const yul = must(run(process.execPath, 'vendor/bend-frontend/host/run.js', 'src/compile.bend', program, ...functions));
    writeFileSync(path.join(temp, 'Contract.yul'), yul);
    const solc = must(run('solc', '--strict-assembly', '--evm-version', 'shanghai', '--bin', path.join(temp, 'Contract.yul')));
    bytecode = solc.split('Binary representation:')[1].trim();
  }

  const node = Bun.spawn(['anvil', '--host', '127.0.0.1', '--port', '0'], { stdout: 'pipe', stderr: 'pipe' });
  const reader = node.stdout.getReader();
  let output = '';
  let rpc;
  while (!rpc) {
    const chunk = await reader.read();
    if (chunk.done) throw new Error('anvil stopped before it listened');
    output += new TextDecoder().decode(chunk.value);
    const port = output.match(/Listening on 127\.0\.0\.1:(\d+)/)?.[1];
    if (port) rpc = `http://127.0.0.1:${port}`;
  }
  reader.releaseLock();

  const cast = (command, ...args) => run('cast', command, '--rpc-url', rpc, ...args);
  const fund = who => {
    must(cast('rpc', 'anvil_impersonateAccount', who));
    must(cast('rpc', 'anvil_setBalance', who, '0x56bc75e2d63100000'));
  };
  if (deployer) fund(deployer);
  const sender = deployer ?? must(cast('rpc', 'eth_accounts')).match(/0x[0-9a-fA-F]{40}/)[0];
  const receipt = JSON.parse(must(cast('send', '--unlocked', '--from', sender, '--json', '--create', '0x' + bytecode + args.map(x => x.toString(16).padStart(64, '0')).join(''))));
  const address = receipt.contractAddress;
  fund(owner);
  return {
    cast, sender, address, fund, receipt, bytecode,
    send: (from, ...args) => cast('send', '--unlocked', '--from', from, address, ...args),
    word: (...args) => BigInt(must(cast('call', address, ...args)).split(' ')[0]),
    async stop() {
      node.kill();
      await node.exited;
      rmSync(temp, { recursive: true, force: true });
    },
  };
}
