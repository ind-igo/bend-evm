import { existsSync, mkdirSync, writeFileSync } from 'node:fs';
import path from 'node:path';

// Certifies, checks and compiles a contract: the Yul goes to stdout only when
// the certificate for the same entries checks, and PROOF.bend too if the
// contract has one. With --out <prefix>, it writes <prefix>.yul, the deploy
// bytecode <prefix>.bin (from solc) and the ABI <prefix>.abi.json instead.
// Usage: bun run build [--out <prefix>] <contract.bend> <function>...
const argv = process.argv.slice(2);
const at = argv.indexOf('--out');
const out = at < 0 ? undefined : argv.splice(at, 2)[1];
const [program, ...entries] = argv;
if (!program || entries.length === 0 || (at >= 0 && !out)) {
  console.error('Usage: bun run build [--out <prefix>] <contract.bend> <function>...');
  process.exit(2);
}
const bend = (...args) => {
  const child = Bun.spawnSync([process.execPath, ...args], { stdout: 'pipe', stderr: 'inherit' });
  if (child.exitCode !== 0) process.exit(child.exitCode ?? 1);
  return child.stdout.toString();
};
const run = 'vendor/bend-frontend/host/run.js';
const main = 'vendor/bend-frontend/vendor/bend/bend2/main.ts';
const dir = path.dirname(program);
const cert = path.join(dir, 'CERT.bend');
writeFileSync(cert, bend(run, 'src/certify.bend', program, ...entries));
for (const file of [cert, path.join(dir, 'PROOF.bend')].filter(existsSync)) {
  const out = bend(main, file, '--check-only');
  if (!out.includes('All terms check.')) {
    console.error(out);
    process.exit(1);
  }
}
const yul = bend(run, 'src/compile.bend', program, ...entries);
if (!out) {
  process.stdout.write(yul);
  process.exit(0);
}
mkdirSync(path.dirname(out), { recursive: true });
writeFileSync(out + '.yul', yul);
const solc = Bun.spawnSync(['solc', '--strict-assembly', '--evm-version', 'shanghai', '--bin', out + '.yul'],
  { stdout: 'pipe', stderr: 'inherit' });
if (solc.exitCode !== 0) process.exit(solc.exitCode ?? 1);
writeFileSync(out + '.bin', solc.stdout.toString().split('Binary representation:')[1].trim() + '\n');
writeFileSync(out + '.abi.json', bend(run, 'src/abi.bend', program, ...entries));
for (const suffix of ['.yul', '.bin', '.abi.json']) console.log(out + suffix);
