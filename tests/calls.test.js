import { afterAll, beforeAll, expect, test } from 'bun:test';
import { readFileSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { bend, check, entries, sandbox } from '../scripts/tools.js';
import { deploy, must } from './chain.js';

let chain;

beforeAll(async () => {
  chain = await deploy({ program: 'tests/fixtures/calls/program.bend', functions: entries.calls });
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
  sandbox(['src', 'tests/fixtures/calls'], dir => {
    const cert = path.join(dir, 'tests/fixtures/calls/CERT.bend');
    const certify = () => {
      writeFileSync(cert, must(bend(path.join(dir, 'src/certify.bend'),
        path.join(dir, 'tests/fixtures/calls/program.bend'), ...entries.calls)));
      const checked = check(cert);
      return checked.out + checked.err;
    };
    expect(certify()).toContain('All terms check.');
    const inline = path.join(dir, 'src/inline.bend');
    const good = readFileSync(inline, 'utf8');
    expect(good).toContain('Done{subst(rest, level, v)}');
    writeFileSync(inline, good.replace('Done{subst(rest, level, v)}', 'Done{rest}'));
    expect(certify()).toContain('Location: run');
  });
}, 300_000);
