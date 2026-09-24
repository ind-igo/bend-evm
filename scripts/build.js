import { existsSync, writeFileSync } from 'node:fs';
import path from 'node:path';

// Certifies, checks and compiles a contract: the Yul goes to stdout only when
// the certificate for the same entries checks, and PROOF.bend too if the
// contract has one. Usage: bun run build <contract.bend> <function>...
const [program, ...entries] = process.argv.slice(2);
if (!program || entries.length === 0) {
  console.error('Usage: bun run build <contract.bend> <function>...');
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
process.stdout.write(bend(run, 'src/compile.bend', program, ...entries));
