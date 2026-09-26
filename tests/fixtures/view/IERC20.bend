import Base
import ../../../src/Evm.bend as Evm

# Interface defs for the view functions of another ERC-20. The first
# parameter is the token's address; the reader takes the signature from the
# name and the other parameter types, and the certificate checks each body.

def totalSupply(token: Evm.Address) -> Evm.Call:
  Evm.Call{token, "totalSupply()", []}

def balanceOf(token: Evm.Address, who: Evm.Address) -> Evm.Call:
  Evm.Call{token, "balanceOf(address)", [who]}
