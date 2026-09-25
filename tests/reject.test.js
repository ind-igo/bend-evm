import { expect, test } from 'bun:test';
import { bend } from '../scripts/tools.js';

// Programs that the reader or the printer must reject, with their errors.
const cases = [
  ['tests/fixtures/init.bend', ['plain'], 'Expected an Evm.Contract result'],
  ['examples/counter/program.bend', ['missing'], 'Unknown contract function'],
  ['tests/fixtures/init.bend', ['init'], 'init must return Unit'],
  ['tests/fixtures/init.bend', ['poke'], 'a storage slot that is not a literal'],
  ['tests/fixtures/meta.bend', ['decimals', 'a'.repeat(134)], 'signatures over 135 bytes are not supported'],
  ['tests/fixtures/emit/bad.bend', ['late'], 'Indexed event fields must come before the others'],
  ['tests/fixtures/emit/bad.bend', ['wide'], 'at most three indexed words'],
  ['tests/fixtures/emit/bad.bend', ['plain'], 'whose result type is Evm.Event'],
  ['tests/fixtures/emit/bad.bend', ['raw'], 'whose result type is Evm.Event'],
  ['tests/fixtures/branch/bad.bend', ['early'], 'A branch must be the last step'],
  ['tests/fixtures/branch/bad.bend', ['middle'], 'A call to a function that branches must be the last step'],
];

for (const [file, functions, error] of cases) {
  test(`compile rejects ${file} ${functions.join(' ').slice(0, 40)}`, () => {
    const result = bend('src/compile.bend', file, ...functions);
    expect(result.ok).toBe(false);
    expect(result.err).toContain(error);
  }, 120_000);
}
