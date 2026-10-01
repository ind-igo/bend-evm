import Base
import ../../src/Evm.bend as Evm

# The call that a flash swap makes to its receiver, as Uniswap V2's
# IUniswapV2Callee. It returns nothing.

def uniswapV2Call(target: Evm.Address, sender: Evm.Address, amount0: Nat, amount1: Nat, data: Evm.Bytes) -> Evm.Call:
  Evm.Call{target, "uniswapV2Call", Evm.abi([Evm.Word{sender}, Evm.Word{amount0}, Evm.Word{amount1}, Evm.Dynamic{data}])}
