// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// The reference for examples/weth/WETH.bend: solmate's WETH on an ERC-20
// with the same events. A failed send of ether reverts with no data, as in
// the Bend contract.
contract WETH {
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    string public constant name = "Wrapped Ether";
    string public constant symbol = "WETH";
    uint8 public constant decimals = 18;

    event Transfer(address indexed from, address indexed to, uint256 amount);
    event Approval(address indexed owner, address indexed spender, uint256 amount);
    event Deposit(address indexed from, uint256 amount);
    event Withdrawal(address indexed to, uint256 amount);

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

    function deposit() public payable {
        totalSupply += msg.value;
        balanceOf[msg.sender] += msg.value;
        emit Transfer(address(0), msg.sender, msg.value);
        emit Deposit(msg.sender, msg.value);
    }

    function withdraw(uint256 amount) external {
        balanceOf[msg.sender] -= amount;
        totalSupply -= amount;
        emit Transfer(msg.sender, address(0), amount);
        emit Withdrawal(msg.sender, amount);
        (bool ok,) = msg.sender.call{value: amount}("");
        if (!ok) revert();
    }

    receive() external payable {
        deposit();
    }
}

interface IWETH {
    function deposit() external payable;
    function withdraw(uint256 amount) external;
}

// An account that holds wrapped ether and can misbehave when it gets ether.
// 0: accept. 1: revert. 2: deposit what it got again. 3: withdraw one more
// wei, once, and ignore a failure.
contract Holder {
    IWETH public weth;
    uint256 public mode;
    bool private inside;

    constructor(IWETH w) {
        weth = w;
    }

    function setMode(uint256 m) external {
        mode = m;
    }

    function deposit() external payable {
        weth.deposit{value: msg.value}();
    }

    function withdraw(uint256 amount) external {
        weth.withdraw(amount);
    }

    receive() external payable {
        if (msg.sender != address(weth) || inside) return;
        require(mode != 1, "no");
        inside = true;
        if (mode == 2) weth.deposit{value: msg.value}();
        if (mode == 3) try weth.withdraw(1) {} catch {}
        inside = false;
    }
}
