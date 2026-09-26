import { expect, test } from 'bun:test';
import { readFileSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { check, sandbox } from '../scripts/tools.js';

// Each mutation keeps yul.bend well typed, so only the preservation proof
// in src/PROOF.bend can reject it.
test('the preservation proof rejects a wrong lowering', () => {
  const files = ['Evm.bend', 'ir.bend', 'yul.bend', 'nat.bend', 'LAWS.bend', 'PROOF.bend'];
  sandbox(files.map(f => `src/${f}`), dir => {
    const src = path.join(dir, 'src');
    writeFileSync(path.join(src, 'probe.bend'), 'import Base\nimport ./yul.bend as Yul\n\ndef main() -> Nat:\n  0n\n');
    // The copy must check before it is broken, or a missing file would pass the test.
    expect(check(path.join(src, 'PROOF.bend')).out).toContain('All terms check.');
    const yul = readFileSync(path.join(src, 'yul.bend'), 'utf8');
    for (const [from, to] of [
      ['    case IR.SLoad{loc}:\n      SLoad{loc}', '    case IR.SLoad{loc}:\n      Caller{}'],
      ['      Lt{Atom{left}, Atom{right}}\n', '      Lt{Atom{right}, Atom{left}}\n'],
      ['      IsZero{lower.test(c)}', '      lower.test(c)'],
      ['def lower.cond(c: IR.Cond) -> Exp:\n  IsZero{lower.test(c)}', 'def lower.cond(c: IR.Cond) -> Exp:\n  lower.test(c)'],
      ['      Evm.time.of(Evm.world.of(s))', '      Evm.chain.of(Evm.world.of(s))'],
      ['Gt{Atom{right}, Sub{', 'Lt{Atom{right}, Sub{'],
      ['Nat.sub(Nat.sub(l, 1n), x)', 'Nat.sub(l, x)'],
      ['Check{Lt{Atom{left}, Atom{right}}, Let{', 'Check{Lt{Atom{right}, Atom{left}}, Let{'],
      ['Log{event, topics, data, lower(body, o)}', 'lower(body, o)'],
      ['Guard{lower.cond(c), error, args, lower(body, o)}', 'Check{lower.cond(c), lower(body, o)}'],
      ['Guard{lower.cond(c), error, args, Stop{}}', 'Guard{lower.test(c), error, args, Stop{}}'],
      ['Bool.pick(Nat, Nat.is_eq(c, 0n), n, y)', 'Bool.pick(Nat, Nat.is_eq(c, 0n), y, n)'],
      ['Not{Atom{IR.Lit{0n}}}', 'Atom{IR.Lit{0n}}'],
      ['If{lower.test(c), lower(yes, o), lower(no, o)}', 'If{lower.test(c), lower(no, o), lower(yes, o)}'],
      ['exec(no, o, env), exec(yes, o, env), R, k, s)', 'exec(yes, o, env), exec(no, o, env), R, k, s)'],
    ]) {
      expect(yul).toContain(from);
      writeFileSync(path.join(src, 'yul.bend'), yul.replace(from, to));
      expect(check(path.join(src, 'probe.bend')).out).toContain('All terms check.');
      const proof = check(path.join(src, 'PROOF.bend'));
      expect(proof.ok).toBe(false);
      expect(proof.out + proof.err).toContain('Location:');
    }
  });
}, 300_000);
