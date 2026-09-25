import { checkUpstream } from '../vendor/bend-frontend/host/adapter.js';
import { checker, root } from './tools.js';

// Checks every committed proof and certificate, and every Bend tool.
checkUpstream();
for (const file of ['src/PROOF.bend',
  'examples/counter/PROOF.bend', 'examples/counter/CERT.bend',
  'examples/token/PROOF.bend', 'examples/token/CERT.bend',
  'tests/fixtures/branch/PROOF.bend', 'tests/fixtures/branch/CERT.bend', 'tests/fixtures/emit/CERT.bend',
  'tests/fixtures/model/token.bend', 'src/certify.bend', 'src/compile.bend', 'src/abi.bend', 'src/selector.bend']) {
  const child = Bun.spawnSync([process.execPath, checker, file, '--check-only'],
    { cwd: root, stdout: 'inherit', stderr: 'inherit' });
  if (child.error) throw child.error;
  if (child.exitCode !== 0) process.exit(child.exitCode ?? 1);
}
