import { checkUpstream, compiled } from '../vendor/bend-frontend/host/adapter.js';
import { checker, root } from './tools.js';

// Checks every committed proof and certificate, and every Bend tool.
checkUpstream();
for (const file of ['src/PROOF.bend',
  'examples/counter/PROOF.bend', 'examples/counter/CERT.bend',
  'examples/erc20/PROOF.bend', 'examples/erc20/CERT.bend',
  'tests/fixtures/branch/PROOF.bend', 'tests/fixtures/branch/CERT.bend', 'tests/fixtures/emit/CERT.bend',
  'tests/fixtures/view/PROOF.bend', 'tests/fixtures/view/CERT.bend',
  'tests/fixtures/vault/PROOF.bend', 'tests/fixtures/vault/CERT.bend',
  'tests/fixtures/math/CERT.bend', 'tests/fixtures/model/math.bend',
  'tests/fixtures/model/token.bend', 'tests/fixtures/model/vault.bend', 'src/selector.bend']) {
  const child = Bun.spawnSync([process.execPath, checker, file, '--check-only'],
    { cwd: root, stdout: 'inherit', stderr: 'inherit' });
  if (child.error) throw child.error;
  if (child.exitCode !== 0) process.exit(child.exitCode ?? 1);
}
// These tools read contracts through the frontend's foreign effects, which the
// verdict refuses; check them as programs, as the frontend checks its CLI.
for (const tool of ['src/certify.bend', 'src/compile.bend', 'src/abi.bend']) {
  try {
    await compiled(`${root}/${tool}`, false);
  } catch (error) {
    console.error(error.message);
    process.exit(1);
  }
}
