import { expect } from 'bun:test';
import { bend, bytecode, must, run } from '../scripts/tools.js';

export { must, run } from '../scripts/tools.js';

// Deploys a contract on a local anvil chain with real transactions, and calls
// it through the standard ABI with cast.

// A failed command must be a revert, not a cast usage error. With an error
// signature, the revert data must start with that error's selector; with
// its arguments too, it must be that whole encoding.
export function reverts(result, error, ...args) {
  expect(result.ok).toBe(false);
  expect(result.err).toMatch(/revert/i);
  if (!error) return;
  const data = args.length ? must(run('cast', 'calldata', error, ...args)) : must(run('cast', 'sig', error));
  expect(result.err).toContain(`data: "${data}${args.length ? '"' : ''}`);
}

// Compiled bytecode, once per program and entry list in this process.
const compiled = new Map();
function code(program, functions) {
  const key = [program, ...functions].join(' ');
  if (!compiled.has(key)) compiled.set(key, bytecode(must(bend('src/compile.bend', program, ...functions))));
  return compiled.get(key);
}

// Resolves to anvil's RPC URL once it listens. It keeps reading anvil's log
// after that, so the pipe never fills.
async function listen(node) {
  const reader = node.stdout.getReader();
  let output = '';
  for (;;) {
    const chunk = await reader.read();
    if (chunk.done) throw new Error('anvil stopped before it listened');
    output += new TextDecoder().decode(chunk.value);
    const port = output.match(/Listening on 127\.0\.0\.1:(\d+)/)?.[1];
    if (port) {
      (async () => { while (!(await reader.read()).done); })();
      return `http://127.0.0.1:${port}`;
    }
  }
}

// Deploys program's functions, or the given bytecode, with the constructor
// arguments as words after the code. The deployer is anvil's first account
// unless given.
export async function deploy({ program, functions, bytecode: given, deployer, args = [] }) {
  const deployed = given ?? code(program, functions);
  const node = Bun.spawn(['anvil', '--host', '127.0.0.1', '--port', '0'], { stdout: 'pipe', stderr: 'ignore' });
  const stop = async () => {
    node.kill();
    await node.exited;
  };
  try {
    const rpc = await listen(node);
    const cast = (command, ...rest) => run('cast', command, '--rpc-url', rpc, ...rest);
    const fund = who => {
      must(cast('rpc', 'anvil_impersonateAccount', who));
      must(cast('rpc', 'anvil_setBalance', who, '0x56bc75e2d63100000'));
    };
    if (deployer) fund(deployer);
    const sender = deployer ?? must(cast('rpc', 'eth_accounts')).match(/0x[0-9a-fA-F]{40}/)[0];
    const words = args.map(x => x.toString(16).padStart(64, '0')).join('');
    const receipt = JSON.parse(must(cast('send', '--unlocked', '--from', sender, '--json', '--create',
      '0x' + deployed + words)));
    const address = receipt.contractAddress;
    return {
      cast, sender, address, fund, receipt, bytecode: deployed, stop,
      send: (from, ...rest) => cast('send', '--unlocked', '--from', from, address, ...rest),
      word: (...rest) => BigInt(must(cast('call', address, ...rest)).split(' ')[0]),
    };
  } catch (error) {
    await stop();
    throw error;
  }
}
