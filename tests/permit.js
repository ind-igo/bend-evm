import { must, run } from './chain.js';

// EIP-2612 signing with cast, for anvil's well-known test accounts.
export const keys = {
  '0x70997970c51812dc3a010c7d01b50e0d17dc79c8': '0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d',
  '0x3c44cdddb6a900fa2b585dd299e03d12fa4293bc': '0x5de4111afa1a4b94908f83103eb1f1706367c2e68ca870fc3fb9a804cdab365a',
  '0x90f79bf6eb2c4f870365e785982e1f101e93b906': '0x7c852118294e51e653712a81e05800f419141751be58f605c371e15141b007a6',
};
const cast = (...args) => must(run('cast', ...args));
export const permitType = cast('keccak', 'Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)');
const domainType = cast('keccak', 'EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)');

// The separator a token named name at address on chain should have.
export function separator(name, chain, address) {
  return cast('keccak', cast('abi-encode', 'f(bytes32,bytes32,bytes32,uint256,address)', domainType,
    cast('keccak', name), cast('keccak', '1'), String(chain), address));
}

// The v, r and s of key's permit, over the token's separator.
export function sign(key, domain, owner, spender, value, nonce, deadline) {
  const message = cast('keccak', cast('abi-encode', 'f(bytes32,address,address,uint256,uint256,uint256)', permitType,
    owner, spender, String(value), String(nonce), String(deadline)));
  const digest = cast('keccak', '0x1901' + domain.slice(2) + message.slice(2));
  const signature = cast('wallet', 'sign', '--no-hash', '--private-key', key, digest).slice(2);
  return [String(parseInt(signature.slice(128, 130), 16)), '0x' + signature.slice(0, 64), '0x' + signature.slice(64, 128)];
}
