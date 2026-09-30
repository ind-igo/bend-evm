import Base
import ../../src/Evm.bend as Evm
import ../erc20/ERC20.bend as ERC20
import ./IERC20.bend as IERC20
import ./Math.bend as Math

# A constant-product pair of two tokens, after Uniswap V2's UniswapV2Pair,
# with the 0.3% fee. The pair holds its reserves of the two tokens, and its
# liquidity token is the ERC20 core. As in Uniswap, a user first sends
# tokens to the pair, then calls mint or swap; for burn, the user first
# sends liquidity tokens to the pair.
#
# There is no lock. A token may call back into the pair from a transfer,
# and LAWS.bend proves that x·y still does not go down.
#
# Not here: the price oracle, flash swaps, skim, the protocol fee and the
# 112-bit reserves. Reserves are full words, and the checked arithmetic
# reverts where a product would overflow.

# Storage after the ERC20 core.
def TOKEN0() -> Nat:
  3n

def TOKEN1() -> Nat:
  4n

def RESERVE0() -> Nat:
  5n

def RESERVE1() -> Nat:
  6n

# The liquidity that the first mint locks at address zero.
def MINIMUM_LIQUIDITY() -> Nat:
  1000n

# Events, with the indexed parameters first.
def Mint(sender: Evm.Indexed(Evm.Address), amount0: Nat, amount1: Nat) -> Evm.Log:
  Evm.Log{"Mint", [sender], [amount0, amount1]}

def Burn(sender: Evm.Indexed(Evm.Address), to: Evm.Indexed(Evm.Address), amount0: Nat, amount1: Nat) -> Evm.Log:
  Evm.Log{"Burn", [sender, to], [amount0, amount1]}

def Swap(sender: Evm.Indexed(Evm.Address), to: Evm.Indexed(Evm.Address), amount0In: Nat, amount1In: Nat,
  amount0Out: Nat, amount1Out: Nat) -> Evm.Log:
  Evm.Log{"Swap", [sender, to], [amount0In, amount1In, amount0Out, amount1Out]}

def Sync(reserve0: Nat, reserve1: Nat) -> Evm.Log:
  Evm.Log{"Sync", [], [reserve0, reserve1]}

# The results of getReserves.
def Reserves(reserve0: Nat, reserve1: Nat) -> Evm.Values:
  Evm.Values{[reserve0, reserve1]}

# Errors, with the names of Uniswap's messages.
def InsufficientLiquidityMinted() -> Evm.Error:
  Evm.Error{"InsufficientLiquidityMinted", []}

def InsufficientLiquidityBurned() -> Evm.Error:
  Evm.Error{"InsufficientLiquidityBurned", []}

def InsufficientOutputAmount() -> Evm.Error:
  Evm.Error{"InsufficientOutputAmount", []}

def InsufficientInputAmount() -> Evm.Error:
  Evm.Error{"InsufficientInputAmount", []}

def InsufficientLiquidity() -> Evm.Error:
  Evm.Error{"InsufficientLiquidity", []}

def InvalidTo() -> Evm.Error:
  Evm.Error{"InvalidTo", []}

def TransferFailed() -> Evm.Error:
  Evm.Error{"TransferFailed", []}

def K() -> Evm.Error:
  Evm.Error{"K", []}

def name() -> String:
  "Bend LP"

def symbol() -> String:
  "BLP"

def decimals() -> Evm.Contract(Evm.Uint8):
  Evm.Contract.pure(Nat, 18n)

def totalSupply() -> Evm.Contract(Nat):
  ERC20.totalSupply()

def balanceOf(who: Evm.Address) -> Evm.Contract(Nat):
  ERC20.balanceOf(who)

def allowance(holder: Evm.Address, spender: Evm.Address) -> Evm.Contract(Nat):
  ERC20.allowance(holder, spender)

def approve(+spender: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  ERC20.approve(spender, amount)

def transfer(+to: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  ERC20.transfer(to, amount)

def transferFrom(+from: Evm.Address, +to: Evm.Address, +amount: Nat) -> Evm.Contract(Evm.Boolean):
  ERC20.transferFrom(from, to, amount)

def init(+token0: Evm.Address, +token1: Evm.Address) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    Evm.sstore(TOKEN0(), token0)
    Evm.sstore(TOKEN1(), token1)

def token0() -> Evm.Contract(Evm.Address):
  Evm.sload(TOKEN0())

def token1() -> Evm.Contract(Evm.Address):
  Evm.sload(TOKEN1())

def reserve0() -> Evm.Contract(Nat):
  Evm.sload(RESERVE0())

def reserve1() -> Evm.Contract(Nat):
  Evm.sload(RESERVE1())

def getReserves() -> Evm.Contract(Evm.Values):
  do Evm.Contract<Evm.Values>:
    r0 : Nat <- Evm.sload(RESERVE0())
    r1 : Nat <- Evm.sload(RESERVE1())
    Evm.Contract.pure(Evm.Values, Reserves(r0, r1))

# Sends amount of token to to. The token must return true.
def pay(+token: Nat, +to: Nat, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    ok : Nat <- Evm.call(IERC20.transfer(token, to, amount))
    Evm.ensure(Nat.is_eq(ok, 1n), TransferFailed())

# The new reserves.
def update(+balance0: Nat, +balance1: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    Evm.sstore(RESERVE0(), balance0)
    Evm.sstore(RESERVE1(), balance1)
    Evm.emit(Sync(balance0, balance1))

# The pair's balances of its two tokens become the reserves.
def sync() -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +me : Nat <- Evm.self()
    +t0 : Nat <- Evm.sload(TOKEN0())
    +t1 : Nat <- Evm.sload(TOKEN1())
    +balance0 : Nat <- Evm.view(IERC20.balanceOf(t0, me))
    +balance1 : Nat <- Evm.view(IERC20.balanceOf(t1, me))
    update(balance0, balance1)

# The end of a mint: gives to the liquidity, which must not be zero.
def minted(+to: Nat, +balance0: Nat, +balance1: Nat, +amount0: Nat, +amount1: Nat, +liquidity: Nat) ->
  Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    Evm.ensure(Nat.is_lt(0n, liquidity), InsufficientLiquidityMinted())
    ERC20.mint(to, liquidity)
    update(balance0, balance1)
    +who : Nat <- Evm.caller()
    Evm.emit(Mint(who, amount0, amount1))
    Evm.Contract.pure(Nat, liquidity)

# The first mint: the geometric mean of the amounts, less the minimum
# liquidity, which stays locked at address zero.
def first(+to: Nat, +balance0: Nat, +balance1: Nat, +amount0: Nat, +amount1: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +product : Nat <- Evm.mul(amount0, amount1)
    +root : Nat <- Math.sqrt(product)
    +liquidity : Nat <- Evm.sub(root, MINIMUM_LIQUIDITY())
    ERC20.mint(0n, MINIMUM_LIQUIDITY())
    minted(to, balance0, balance1, amount0, amount1, liquidity)

# A later mint: the smaller share of the supply that the amounts buy.
def more(+to: Nat, +balance0: Nat, +balance1: Nat, +amount0: Nat, +amount1: Nat, +r0: Nat, +r1: Nat,
  +supply: Nat) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +x : Nat <- Evm.mul(amount0, supply)
    +share0 : Nat <- Evm.div(x, r0)
    +y : Nat <- Evm.mul(amount1, supply)
    +share1 : Nat <- Evm.div(y, r1)
    +liquidity : Nat <- Evm.select(Nat.is_lt(share0, share1), share0, share1)
    minted(to, balance0, balance1, amount0, amount1, liquidity)

# Gives to liquidity tokens for the tokens sent to the pair since the last
# update, and returns their number.
def mint(+to: Evm.Address) -> Evm.Contract(Nat):
  do Evm.Contract<Nat>:
    +me : Nat <- Evm.self()
    +t0 : Nat <- Evm.sload(TOKEN0())
    +t1 : Nat <- Evm.sload(TOKEN1())
    +balance0 : Nat <- Evm.view(IERC20.balanceOf(t0, me))
    +balance1 : Nat <- Evm.view(IERC20.balanceOf(t1, me))
    +r0 : Nat <- Evm.sload(RESERVE0())
    +r1 : Nat <- Evm.sload(RESERVE1())
    +amount0 : Nat <- Evm.sub(balance0, r0)
    +amount1 : Nat <- Evm.sub(balance1, r1)
    +supply : Nat <- Evm.sload(ERC20.SUPPLY())
    Evm.branch(Nat, Nat.is_eq(supply, 0n), first(to, balance0, balance1, amount0, amount1),
      more(to, balance0, balance1, amount0, amount1, r0, r1, supply))

# Burns the liquidity tokens that the pair holds, and sends to its share
# of each token.
def burn(+to: Evm.Address) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    +me : Nat <- Evm.self()
    +t0 : Nat <- Evm.sload(TOKEN0())
    +t1 : Nat <- Evm.sload(TOKEN1())
    +balance0 : Nat <- Evm.view(IERC20.balanceOf(t0, me))
    +balance1 : Nat <- Evm.view(IERC20.balanceOf(t1, me))
    +liquidity : Nat <- Evm.load(ERC20.BALANCES(), me)
    +supply : Nat <- Evm.sload(ERC20.SUPPLY())
    +x : Nat <- Evm.mul(liquidity, balance0)
    +amount0 : Nat <- Evm.div(x, supply)
    +y : Nat <- Evm.mul(liquidity, balance1)
    +amount1 : Nat <- Evm.div(y, supply)
    Evm.ensure(Nat.is_lt(0n, amount0), InsufficientLiquidityBurned())
    Evm.ensure(Nat.is_lt(0n, amount1), InsufficientLiquidityBurned())
    ERC20.burn(me, liquidity)
    pay(t0, to, amount0)
    pay(t1, to, amount1)
    sync()
    Evm.emit(Burn(who, to, amount0, amount1))

# The check at the end of a swap, on the balances after the tokens went out.
def check(+who: Nat, +to: Nat, +amount0Out: Nat, +amount1Out: Nat, +r0: Nat, +r1: Nat, +balance0: Nat,
  +balance1: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +left0 : Nat <- Evm.sub(r0, amount0Out)
    +left1 : Nat <- Evm.sub(r1, amount1Out)
    +more0 : Nat <- Evm.unchecked.sub(balance0, left0)
    +more1 : Nat <- Evm.unchecked.sub(balance1, left1)
    +amount0In : Nat <- Evm.select(Nat.is_lt(left0, balance0), more0, 0n)
    +amount1In : Nat <- Evm.select(Nat.is_lt(left1, balance1), more1, 0n)
    +into : Nat <- Evm.or(amount0In, amount1In)
    Evm.ensure(Nat.is_lt(0n, into), InsufficientInputAmount())
    +scaled0 : Nat <- Evm.mul(balance0, 1000n)
    +fee0 : Nat <- Evm.mul(amount0In, 3n)
    +adjusted0 : Nat <- Evm.sub(scaled0, fee0)
    +scaled1 : Nat <- Evm.mul(balance1, 1000n)
    +fee1 : Nat <- Evm.mul(amount1In, 3n)
    +adjusted1 : Nat <- Evm.sub(scaled1, fee1)
    +after : Nat <- Evm.mul(adjusted0, adjusted1)
    +before : Nat <- Evm.mul(r0, r1)
    +scaled : Nat <- Evm.mul(before, 1000n)
    +least : Nat <- Evm.mul(scaled, 1000n)
    Evm.ensure(Bool.not(Nat.is_lt(after, least)), K())
    update(balance0, balance1)
    Evm.emit(Swap(who, to, amount0In, amount1In, amount0Out, amount1Out))

# The end of a swap, after the tokens went out.
def settle(+who: Nat, +to: Nat, +amount0Out: Nat, +amount1Out: Nat, +r0: Nat, +r1: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +me : Nat <- Evm.self()
    +t0 : Nat <- Evm.sload(TOKEN0())
    +t1 : Nat <- Evm.sload(TOKEN1())
    +balance0 : Nat <- Evm.view(IERC20.balanceOf(t0, me))
    +balance1 : Nat <- Evm.view(IERC20.balanceOf(t1, me))
    check(who, to, amount0Out, amount1Out, r0, r1, balance0, balance1)

# Sends to the amounts out. The tokens that the caller sent in before, less
# the 0.3% fee, must keep the product of the reserves.
def swap(+amount0Out: Nat, +amount1Out: Nat, +to: Evm.Address) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    +out : Nat <- Evm.or(amount0Out, amount1Out)
    Evm.ensure(Nat.is_lt(0n, out), InsufficientOutputAmount())
    +r0 : Nat <- Evm.sload(RESERVE0())
    +r1 : Nat <- Evm.sload(RESERVE1())
    Evm.ensure(Nat.is_lt(amount0Out, r0), InsufficientLiquidity())
    Evm.ensure(Nat.is_lt(amount1Out, r1), InsufficientLiquidity())
    +t0 : Nat <- Evm.sload(TOKEN0())
    +t1 : Nat <- Evm.sload(TOKEN1())
    Evm.ensure(Bool.not(Nat.is_eq(to, t0)), InvalidTo())
    Evm.ensure(Bool.not(Nat.is_eq(to, t1)), InvalidTo())
    pay(t0, to, amount0Out)
    pay(t1, to, amount1Out)
    settle(who, to, amount0Out, amount1Out, r0, r1)
