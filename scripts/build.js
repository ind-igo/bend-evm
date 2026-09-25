import { existsSync, mkdirSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { bytecode, checker, host, root } from './tools.js';

// Certifies, checks and compiles a contract: the Yul goes to stdout only when
// the certificate for the same entries checks, and PROOF.bend too if the
// contract has one. With --out <prefix>, it writes <prefix>.yul, the deploy
// bytecode <prefix>.bin (from solc) and the ABI <prefix>.abi.json instead.
// Usage: bun run build [--out <prefix>] <contract.bend> <function>...
const argv = process.argv.slice(2);
const at = argv.indexOf('--out');
const out = at < 0 ? undefined : argv.splice(at, 2)[1];
const [given, ...entries] = argv;
if (!given || entries.length === 0 || (at >= 0 && !out)) {
  console.error('Usage: bun run build [--out <prefix>] <contract.bend> <function>...');
  process.exit(2);
}
const program = path.resolve(given);
// A Bend command's stdout; its errors go to stderr, and a failure ends the build.
const bend = (...args) => {
  const child = Bun.spawnSync([process.execPath, ...args], { cwd: root, stdout: 'pipe', stderr: 'inherit' });
  if (child.exitCode !== 0) process.exit(child.exitCode ?? 1);
  return child.stdout.toString();
};
const dir = path.dirname(program);
const cert = path.join(dir, 'CERT.bend');
writeFileSync(cert, bend(host, 'src/certify.bend', program, ...entries));
for (const file of [cert, path.join(dir, 'PROOF.bend')].filter(existsSync)) {
  const out = bend(checker, file, '--check-only');
  if (!out.includes('All terms check.')) {
    console.error(out);
    process.exit(1);
  }
}
const yul = bend(host, 'src/compile.bend', program, ...entries);
if (!out) {
  process.stdout.write(yul);
  process.exit(0);
}
// solc and the ABI run before any file is written, so a failure leaves the
// old outputs as they were.
const bin = bytecode(yul) + '\n';
const abi = bend(host, 'src/abi.bend', program, ...entries);
mkdirSync(path.dirname(out), { recursive: true });
for (const [suffix, text] of [['.yul', yul], ['.bin', bin], ['.abi.json', abi]]) {
  writeFileSync(out + suffix, text);
  console.log(out + suffix);
}
