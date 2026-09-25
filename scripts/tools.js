import { cpSync, mkdtempSync, rmSync, symlinkSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

// What the scripts and the tests share: running commands, the Bend tools and
// solc, temporary copies of the repository, and the entry lists.
export const root = path.resolve(import.meta.dir, '..');
export const host = 'vendor/bend-frontend/host/run.js';
export const checker = 'vendor/bend-frontend/vendor/bend/bend2/main.ts';

// out is trimmed, text is the whole stdout.
export function spawn(argv, { cwd = root, timeout = 300_000, stdin } = {}) {
  const child = Bun.spawnSync(argv, { cwd, timeout, stdin });
  const text = child.stdout.toString();
  return {
    ok: child.exitCode === 0, out: text.trim(), text, err: child.stderr.toString(),
    command: argv.join(' ').slice(0, 200), status: child.exitCode ?? `signal ${child.signalCode}`,
  };
}

export const run = (command, ...args) => spawn([command, ...args]);

export function must(result) {
  if (!result.ok) throw new Error(`${result.command} failed (${result.status})\n${result.err}`);
  return result.out;
}

// A Bend tool with IO, such as src/compile.bend, through the frontend's host.
export const bend = (tool, ...args) => run(process.execPath, host, tool, ...args);

// The checker's verdict; out and err together hold its messages.
export const check = (file, options) => spawn([process.execPath, checker, file, '--check-only'], options);

// The deploy bytecode of a Yul object.
export function bytecode(yul, flags = []) {
  const solc = spawn(['solc', '--strict-assembly', '--evm-version', 'shanghai', ...flags, '--bin', '-'],
    { stdin: new TextEncoder().encode(yul) });
  return must(solc).split('Binary representation:')[1].trim();
}

// Runs fn(dir) in a temporary copy of the given parts of the repository,
// with vendor linked, and removes the copy after it.
export function sandbox(parts, fn) {
  const dir = mkdtempSync(path.join(tmpdir(), 'bend-evm-'));
  try {
    for (const part of parts) cpSync(path.join(root, part), path.join(dir, part), { recursive: true });
    symlinkSync(path.join(root, 'vendor'), path.join(dir, 'vendor'));
    return fn(dir);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

// The entries that each program compiles and certifies.
export const entries = {
  counter: ['get', 'increment', 'decrement', 'set'],
  token: ['name', 'symbol', 'decimals', 'init', 'owner', 'transferOwnership', 'totalSupply', 'balanceOf', 'transfer',
    'mint', 'burn', 'allowance', 'approve', 'transferFrom', 'nonces', 'DOMAIN_SEPARATOR', 'permit'],
  branch: ['init', 'keep', 'grade', 'get', 'mark', 'marked'],
  calls: ['run', 'outer'],
  emit: ['moved'],
};

// The largest word, 2^256 - 1.
export const top = (1n << 256n) - 1n;
