import { checkUpstream } from '../vendor/bend-frontend/host/adapter.js';

checkUpstream();
for (const file of ['yul-u32/PROOF.bend', 'yul-u32/emit.bend',
  'examples/counter/PROOF.bend', 'examples/counter/CERT.bend', 'src/certify.bend']) {
  const child = Bun.spawnSync([process.execPath, 'vendor/bend-frontend/vendor/bend/bend2/main.ts', file, '--check-only'],
    { stdout: 'inherit', stderr: 'inherit' });
  if (child.error) throw child.error;
  if (child.exitCode !== 0) process.exit(child.exitCode ?? 1);
}
