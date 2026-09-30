import { expect, test } from 'bun:test';
import { entries } from '../scripts/tools.js';
import { deploy, must, run } from './chain.js';

// Transient storage (tests/fixtures/transient): poke sets a lock with
// tstore while it calls a hook, and the hook's callback into poke reverts
// with Reentrancy(). The lock is gone in the next transaction.
test('a callback into a guarded function reverts, and the lock clears', async () => {
  const chain = await deploy({ program: 'tests/fixtures/transient/program.bend', functions: entries.transient });
  try {
    const out = must(run('solc', '--evm-version', 'cancun', '--bin', 'tests/fixtures/transient/Hook.sol'));
    const hook = JSON.parse(must(chain.cast('send', '--unlocked', '--from', chain.sender, '--json', '--create',
      '0x' + out.split(':Hook =======')[1].split('Binary:')[1].trim().split('\n')[0]))).contractAddress;
    must(chain.send(chain.sender, 'poke(address)', hook));
    expect(chain.word('count()(uint256)')).toBe(1n);
    expect(chain.word('locked()(uint256)')).toBe(0n);
    expect(BigInt(must(chain.cast('call', hook, 'seen()(uint256)')))).toBe(1n);
    expect(must(chain.cast('call', hook, 'error()(bytes)'))).toBe(must(run('cast', 'sig', 'Reentrancy()')));
  } finally {
    await chain.stop();
  }
}, 120_000);
