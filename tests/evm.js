// The EVM's word operations, after the Yellow Paper, for words of w bits
// (256 on the EVM). It is the reference for the model's operations
// (Evm.op in src/Evm.bend) at a small width and for the compiled code on
// anvil at 256 bits, so each is checked against something written apart.
export const arity = {
  add: 2, sub: 2, mul: 2, div: 2, sdiv: 2, mod: 2, smod: 2, addmod: 3, mulmod: 3, exp: 2, signextend: 2,
  lt: 2, gt: 2, slt: 2, sgt: 2, eq: 2, iszero: 1, and: 2, or: 2, xor: 2, not: 1, byte: 2, shl: 2, shr: 2, sar: 2,
};

export function evm(op, [a, b, c], w = 256) {
  const bits = BigInt(w), size = 1n << bits, mask = size - 1n;
  const word = x => ((x % size) + size) % size;
  const signed = x => x >= size / 2n ? x - size : x;
  const bool = x => x ? 1n : 0n;
  switch (op) {
    case 'add': return word(a + b);
    case 'sub': return word(a - b);
    case 'mul': return word(a * b);
    case 'div': return b === 0n ? 0n : a / b;
    case 'sdiv': return b === 0n ? 0n : word(signed(a) / signed(b));
    case 'mod': return b === 0n ? 0n : a % b;
    case 'smod': return b === 0n ? 0n : word(signed(a) % signed(b));
    case 'addmod': return c === 0n ? 0n : (a + b) % c;
    case 'mulmod': return c === 0n ? 0n : (a * b) % c;
    case 'exp': {
      let r = 1n, x = a;
      for (let e = b; e > 0n; e >>= 1n, x = word(x * x)) if (e & 1n) r = word(r * x);
      return r;
    }
    case 'signextend': {
      if (a >= bits / 8n - 1n) return b;
      const t = 8n * a + 7n, low = (1n << (t + 1n)) - 1n;
      return (b >> t) & 1n ? b | (mask ^ low) : b & low;
    }
    case 'lt': return bool(a < b);
    case 'gt': return bool(a > b);
    case 'slt': return bool(signed(a) < signed(b));
    case 'sgt': return bool(signed(a) > signed(b));
    case 'eq': return bool(a === b);
    case 'iszero': return bool(a === 0n);
    case 'and': return a & b;
    case 'or': return a | b;
    case 'xor': return a ^ b;
    case 'not': return mask ^ a;
    case 'byte': return a >= bits / 8n ? 0n : (b >> (8n * (bits / 8n - 1n - a))) & 0xffn;
    case 'shl': return a >= bits ? 0n : (b << a) & mask;
    case 'shr': return a >= bits ? 0n : b >> a;
    case 'sar': return word(signed(b) >> (a >= bits ? bits : a));
  }
  throw new Error(`unknown operation ${op}`);
}

// Words that find the edges of each operation at w bits, then random ones.
export function words(w, random, count) {
  const bits = BigInt(w), size = 1n << bits, half = size / 2n;
  const edges = [0n, 1n, 2n, 3n, 7n, 8n, 31n, 32n, 33n, bits - 1n, bits, bits + 1n, bits / 8n - 1n, bits / 8n,
    0x80n, 0xffn, 0x7fffn, 0x8000n, half - 1n, half, half + 1n, size - 1n, size - 2n, size - 3n];
  const out = [...edges];
  for (let i = 0; i < count; i++) {
    let x = 0n;
    for (let j = 0; j < w; j += 16) x = (x << 16n) | BigInt(Math.floor(random() * 65536));
    // Some small, some near the top, some of any size.
    const kind = Math.floor(random() * 3);
    out.push(kind === 0 ? x % 300n : kind === 1 ? size - 1n - (x % 300n) : x & (size - 1n));
  }
  return out;
}
