import { bend, bytecode, entries, must, run, top } from './tools.js';
import { deploy } from '../tests/chain.js';
import { keys, separator, sign } from '../tests/permit.js';

// Prints a Markdown table of the gas that each token transaction uses, for
// the Bend token and the Solidity reference (tests/fixtures/reference/Token.sol),
// each without and with the solc optimizer. All four run the same calls on
// one anvil chain. The numbers are receipt gasUsed, with the 21000 base and
// the calldata cost. Usage: bun scripts/gas.js
const word = x => BigInt(x).toString(16).padStart(64, '0');
const yul = must(bend('src/compile.bend', 'examples/token/program.bend', ...entries.token));
const bend0 = bytecode(yul);
const chain = await deploy({ bytecode: bend0, args: [0n] });
const [a, b, c] = Object.keys(keys);
const owner = chain.sender;

function create(code, name) {
  const receipt = JSON.parse(must(chain.cast('send', '--unlocked', '--from', owner, '--json', '--create', '0x' + code)));
  return { name, address: receipt.contractAddress, deploy: BigInt(receipt.gasUsed) };
}

function solidity(flags) {
  const out = must(run('solc', '--evm-version', 'shanghai', ...flags, '--bin', 'tests/fixtures/reference/Token.sol'));
  return out.split('Binary:')[1].trim() + word(0);
}

try {
  const tokens = [
    create(bend0 + word(0), 'Bend'),
    create(bytecode(yul, ['--optimize']) + word(0), 'Bend, optimized'),
    create(solidity([]), 'Solidity'),
    create(solidity(['--optimize', '--optimize-runs', '1000000']), 'Solidity, optimized'),
  ];

  const now = Number(must(chain.cast('block', 'latest', '--field', 'timestamp')));
  const chainId = must(chain.cast('chain-id'));

  // Each step: a label, the sender, and the call. A function gives the call
  // for a token, when it depends on the token's address.
  const steps = [
    ['mint to a new holder', owner, ['mint(address,uint256)', a, '1000']],
    ['mint to a holder', owner, ['mint(address,uint256)', a, '1000']],
    ['transfer to a new holder', a, ['transfer(address,uint256)', b, '100']],
    ['transfer to a holder', a, ['transfer(address,uint256)', b, '100']],
    ['approve', a, ['approve(address,uint256)', c, '500']],
    ['transferFrom, finite allowance', c, ['transferFrom(address,address,uint256)', a, b, '100']],
    ['approve max', a, ['approve(address,uint256)', c, String(top)]],
    ['transferFrom, max allowance', c, ['transferFrom(address,address,uint256)', a, b, '100']],
    ['burn', a, ['burn(uint256)', '100']],
    ['permit', owner, token => {
      const deadline = String(now + 100000);
      const domain = separator('Bend Token', chainId, token.address);
      return ['permit(address,address,uint256,uint256,uint8,bytes32,bytes32)', b, c, '7', deadline,
        ...sign(keys[b], domain, b, c, '7', 0n, deadline)];
    }],
  ];

  for (const who of [a, b, c]) chain.fund(who);
  const rows = [['deploy', ...tokens.map(t => t.deploy)]];
  for (const [label, from, call] of steps) {
    rows.push([label, ...tokens.map(token => {
      const args = typeof call === 'function' ? call(token) : call;
      const receipt = JSON.parse(must(chain.cast('send', '--unlocked', '--from', from, '--json', token.address, ...args)));
      if (receipt.status !== '0x1') throw new Error(`${token.name}: ${label} reverted`);
      return BigInt(receipt.gasUsed);
    })]);
  }
  rows.push(['runtime code (bytes)', ...tokens.map(t => BigInt(must(chain.cast('codesize', t.address))))]);

  console.log(`| | ${tokens.map(t => t.name).join(' | ')} |`);
  console.log(`|---|${tokens.map(() => '---:').join('|')}|`);
  for (const [label, ...values] of rows) console.log(`| ${label} | ${values.join(' | ')} |`);
} finally {
  await chain.stop();
}
