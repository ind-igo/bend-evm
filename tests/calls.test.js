import { afterAll, beforeAll, expect, test } from 'bun:test';
import { cpSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { deploy, must } from './chain.js';

const root = path.resolve(import.meta.dir, '..');
const bend = (...args) => Bun.spawnSync([process.execPath, ...args], { cwd: root, timeout: 120_000 });
let chain;

beforeAll(async () => {
  chain = await deploy('tests/fixtures/calls/program.bend', ['run', 'outer']);
}, 120_000);

afterAll(() => chain?.stop());

test('inlined calls run on the chain', () => {
  must(chain.send(chain.sender, 'run(uint256)', '3'));
  expect(chain.word('run(uint256)(uint256)', '3')).toBe(19n);
  expect(BigInt(must(chain.cast('storage', chain.address, '0')))).toBe(12n);
  expect(BigInt(must(chain.cast('storage', chain.address, '1')))).toBe(19n);
  expect(chain.word('outer(uint256)(uint256)', '5')).toBe(1n);
});

// The reader is not trusted: a wrong inlining gives a certificate that fails.
test('the certificate of the inlined calls checks, and catches a wrong join', () => {
  const dir = mkdtempSync(path.join(tmpdir(), 'bend-evm-calls-'));
  try {
    cpSync(path.join(root, 'src'), path.join(dir, 'src'), { recursive: true });
    cpSync(path.join(root, 'tests/fixtures/calls'), path.join(dir, 'tests/fixtures/calls'), { recursive: true });
    symlinkSync(path.join(root, 'vendor'), path.join(dir, 'vendor'));
    const file = path.join(dir, 'tests/fixtures/calls/CERT.bend');
    const certify = () => {
      const cert = bend('vendor/bend-frontend/host/run.js', path.join(dir, 'src/certify.bend'),
        path.join(dir, 'tests/fixtures/calls/program.bend'), 'run', 'outer');
      expect(cert.exitCode).toBe(0);
      writeFileSync(file, cert.stdout.toString());
      const checked = bend('vendor/bend-frontend/vendor/bend/bend2/main.ts', file, '--check-only');
      return checked.stdout.toString() + checked.stderr.toString();
    };
    expect(certify()).toContain('All terms check.');
    const inline = path.join(dir, 'src/inline.bend');
    const good = readFileSync(inline, 'utf8');
    expect(good).toContain('Done{subst(rest, level, v)}');
    writeFileSync(inline, good.replace('Done{subst(rest, level, v)}', 'Done{rest}'));
    expect(certify()).toContain('Location: run');
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}, 300_000);
