// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// The reference for examples/amm/Pair.bend: Uniswap V2's pair with the same
// changes (no lock, no oracle, no skim, full-word reserves
// and no time in getReserves, custom errors, both transfers always made,
// indexed event parameters first). The square root is Uniswap's Babylonian loop, not the Bend pair's
// Newton steps, so the test checks one against the other.
contract Pair {
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    address public token0;
    address public token1;
    uint256 public reserve0;
    uint256 public reserve1;

    string public constant name = "Bend LP";
    string public constant symbol = "BLP";
    uint8 public constant decimals = 18;
    uint256 constant MINIMUM_LIQUIDITY = 1000;

    event Transfer(address indexed from, address indexed to, uint256 amount);
    event Approval(address indexed owner, address indexed spender, uint256 amount);
    event Mint(address indexed sender, uint256 amount0, uint256 amount1);
    event Burn(address indexed sender, address indexed to, uint256 amount0, uint256 amount1);
    event Swap(address indexed sender, address indexed to, uint256 amount0In, uint256 amount1In, uint256 amount0Out,
        uint256 amount1Out);
    event Sync(uint256 reserve0, uint256 reserve1);

    error InsufficientLiquidityMinted();
    error InsufficientLiquidityBurned();
    error InsufficientOutputAmount();
    error InsufficientInputAmount();
    error InsufficientLiquidity();
    error InvalidTo();
    error TransferFailed();
    error K();

    constructor(address _token0, address _token1) {
        token0 = _token0;
        token1 = _token1;
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        emit Approval(msg.sender, spender, amount);
        return true;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        emit Transfer(msg.sender, to, amount);
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        uint256 allowed = allowance[from][msg.sender];
        if (allowed != type(uint256).max) allowance[from][msg.sender] = allowed - amount;
        balanceOf[from] -= amount;
        balanceOf[to] += amount;
        emit Transfer(from, to, amount);
        return true;
    }

    function _mint(address to, uint256 amount) internal {
        totalSupply += amount;
        balanceOf[to] += amount;
        emit Transfer(address(0), to, amount);
    }

    function _burn(address from, uint256 amount) internal {
        balanceOf[from] -= amount;
        totalSupply -= amount;
        emit Transfer(from, address(0), amount);
    }

    function sqrt(uint256 y) internal pure returns (uint256 z) {
        if (y > 3) {
            z = y;
            uint256 x = y / 2 + 1;
            while (x < z) {
                z = x;
                x = (y / x + x) / 2;
            }
        } else if (y != 0) {
            z = 1;
        }
    }

    function _pay(address token, address to, uint256 amount) internal {
        if (!IERC20(token).transfer(to, amount)) revert TransferFailed();
    }

    function _update(uint256 balance0, uint256 balance1) internal {
        reserve0 = balance0;
        reserve1 = balance1;
        emit Sync(balance0, balance1);
    }

    function getReserves() external view returns (uint256, uint256) {
        return (reserve0, reserve1);
    }

    function sync() public {
        _update(IERC20(token0).balanceOf(address(this)), IERC20(token1).balanceOf(address(this)));
    }

    function mint(address to) external returns (uint256 liquidity) {
        uint256 balance0 = IERC20(token0).balanceOf(address(this));
        uint256 balance1 = IERC20(token1).balanceOf(address(this));
        uint256 amount0 = balance0 - reserve0;
        uint256 amount1 = balance1 - reserve1;
        if (totalSupply == 0) {
            liquidity = sqrt(amount0 * amount1) - MINIMUM_LIQUIDITY;
            _mint(address(0), MINIMUM_LIQUIDITY);
        } else {
            uint256 share0 = amount0 * totalSupply / reserve0;
            uint256 share1 = amount1 * totalSupply / reserve1;
            liquidity = share0 < share1 ? share0 : share1;
        }
        if (liquidity == 0) revert InsufficientLiquidityMinted();
        _mint(to, liquidity);
        _update(balance0, balance1);
        emit Mint(msg.sender, amount0, amount1);
    }

    function burn(address to) external {
        address _token0 = token0;
        address _token1 = token1;
        uint256 balance0 = IERC20(_token0).balanceOf(address(this));
        uint256 balance1 = IERC20(_token1).balanceOf(address(this));
        uint256 liquidity = balanceOf[address(this)];
        uint256 amount0 = liquidity * balance0 / totalSupply;
        uint256 amount1 = liquidity * balance1 / totalSupply;
        if (amount0 == 0) revert InsufficientLiquidityBurned();
        if (amount1 == 0) revert InsufficientLiquidityBurned();
        _burn(address(this), liquidity);
        _pay(_token0, to, amount0);
        _pay(_token1, to, amount1);
        sync();
        emit Burn(msg.sender, to, amount0, amount1);
    }

    function swap(uint256 amount0Out, uint256 amount1Out, address to, bytes calldata data) external {
        if (amount0Out == 0 && amount1Out == 0) revert InsufficientOutputAmount();
        uint256 r0 = reserve0;
        uint256 r1 = reserve1;
        if (amount0Out >= r0) revert InsufficientLiquidity();
        if (amount1Out >= r1) revert InsufficientLiquidity();
        if (to == token0) revert InvalidTo();
        if (to == token1) revert InvalidTo();
        _pay(token0, to, amount0Out);
        _pay(token1, to, amount1Out);
        if (data.length > 0) IUniswapV2Callee(to).uniswapV2Call(msg.sender, amount0Out, amount1Out, data);
        _settle(to, amount0Out, amount1Out, r0, r1);
    }

    function _settle(address to, uint256 amount0Out, uint256 amount1Out, uint256 r0, uint256 r1) private {
        uint256 balance0 = IERC20(token0).balanceOf(address(this));
        uint256 balance1 = IERC20(token1).balanceOf(address(this));
        uint256 amount0In = balance0 > r0 - amount0Out ? balance0 - (r0 - amount0Out) : 0;
        uint256 amount1In = balance1 > r1 - amount1Out ? balance1 - (r1 - amount1Out) : 0;
        if (amount0In == 0 && amount1In == 0) revert InsufficientInputAmount();
        uint256 adjusted0 = balance0 * 1000 - amount0In * 3;
        uint256 adjusted1 = balance1 * 1000 - amount1In * 3;
        if (adjusted0 * adjusted1 < r0 * r1 * 1000 ** 2) revert K();
        _update(balance0, balance1);
        emit Swap(msg.sender, to, amount0In, amount1In, amount0Out, amount1Out);
    }
}

interface IERC20 {
    function balanceOf(address who) external view returns (uint256);
    function transfer(address to, uint256 amount) external returns (bool);
}

interface IPair {
    function sync() external;
    function mint(address to) external returns (uint256);
    function swap(uint256 amount0Out, uint256 amount1Out, address to, bytes calldata data) external;
}

interface IUniswapV2Callee {
    function uniswapV2Call(address sender, uint256 amount0, uint256 amount1, bytes calldata data) external;
}

// A token for the pair test, with balances and no allowances. When the pair
// takes tokens out, the token can misbehave or call back into the pair.
contract Coin {
    mapping(address => uint256) public balanceOf;
    // 0: plain. 1: return false. 2: revert. 3: call sync. 4: send the pair
    // one more token, then swap one of the other token out, to the hook's
    // owner. 5: send the pair one more token, then mint.
    uint256 public mode;
    address public owner;
    bool private inside;

    constructor() {
        owner = msg.sender;
    }

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
    }

    function setMode(uint256 m) external {
        mode = m;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        require(mode != 2, "no");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        if (!inside && msg.sender.code.length > 0 && mode >= 3) {
            inside = true;
            if (mode == 3) IPair(msg.sender).sync();
            if (mode >= 4) balanceOf[msg.sender] += 1;
            if (mode == 4) {
                // Out of whichever token is not this one.
                bool zero = IPairTokens(msg.sender).token0() == address(this);
                try IPair(msg.sender).swap(zero ? 0 : 1, zero ? 1 : 0, owner, "") {} catch {}
            }
            if (mode == 5) try IPair(msg.sender).mint(owner) {} catch {}
            inside = false;
        }
        return mode != 1;
    }
}

interface IPairTokens {
    function token0() external view returns (address);
    function token1() external view returns (address);
}

// The receiver of flash swaps. The data says what to pay back: pay0 and
// pay1 of each token, which it mints to the pair, and a mode. 0: pay. 1:
// revert. 2: pay, then flash swap one token out again, paying it back with
// one more, inside the call.
contract Borrower {
    function uniswapV2Call(address, uint256, uint256, bytes calldata data) external {
        (uint256 pay0, uint256 pay1, uint256 mode) = abi.decode(data, (uint256, uint256, uint256));
        require(mode != 1, "no");
        address token0 = IPairTokens(msg.sender).token0();
        address token1 = IPairTokens(msg.sender).token1();
        Coin(token0).mint(msg.sender, pay0);
        Coin(token1).mint(msg.sender, pay1);
        if (mode == 2) try IPair(msg.sender).swap(1, 0, address(this), abi.encode(uint256(3), uint256(0), uint256(0))) {} catch {}
    }
}
