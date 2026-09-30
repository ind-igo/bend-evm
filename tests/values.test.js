import { expect, test } from 'bun:test';
import { bend, entries } from '../scripts/tools.js';
import { deploy, must, reverts, run } from './chain.js';

// Several words (tests/fixtures/values): a function that returns a tuple,
// view calls that give several words, and a failed call whose revert data
// the contract passes on.
test('tuples, views of several words, and revert data passed on', async () => {
  const chain = await deploy({ program: 'tests/fixtures/values/program.bend', functions: entries.values });
  try {
    const out = must(run('solc', '--evm-version', 'cancun', '--bin', 'tests/fixtures/values/Source.sol'));
    const source = JSON.parse(must(chain.cast('send', '--unlocked', '--from', chain.sender, '--json', '--create',
      '0x' + out.split(':Source =======')[1].split('Binary:')[1].trim().split('\n')[0]))).contractAddress;
    expect(must(chain.cast('call', chain.address, 'reserves(address)(uint256,uint256)', source))).toBe('11\n22');
    expect(chain.word('total(address)(uint256)', source)).toBe(44n);
    reverts(chain.cast('call', chain.address, 'failing(address)(uint256)', source), 'Nope(uint256)', '7');
    // A target with no code returns no words, so the call reverts with no data.
    const empty = chain.cast('call', chain.address, 'reserves(address)(uint256,uint256)', chain.sender);
    reverts(empty);
    expect(empty.err).toContain('data: "0x"');
  } finally {
    await chain.stop();
  }
}, 120_000);

test('the ABI names a tuple result after its def', () => {
  const abi = JSON.parse(must(bend('src/abi.bend', 'tests/fixtures/values/program.bend', ...entries.values)));
  expect(abi.find(item => item.name === 'reserves')).toEqual({ type: 'function', name: 'reserves',
    inputs: [{ name: 'target', type: 'address' }], outputs: [{ name: 'reserve0', type: 'uint256' },
      { name: 'reserve1', type: 'uint256' }], stateMutability: 'view' });
}, 120_000);
