// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface Vault {
    function deposit(uint256 amount) external;
    function withdraw(uint256 amount) external;
    function totalShares() external view returns (uint256);
}

// A token for the vault test, with balances and no allowances. Before a
// transfer or a transferFrom it can call back into the vault that called it.
contract Hook {
    mapping(address => uint256) public balanceOf;
    // 0: plain. 1: deposit half the amount again. 2: try a deposit, which
    // writes and then reverts as its own transferFrom returns false, and
    // catch it. 3: return false. 4: revert. 5: return no data. 6: ping
    // reads the vault back. 7: withdraw the amount again, from the hook.
    uint256 public mode;
    bool private inside;

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
    }

    function setMode(uint256 m) external {
        mode = m;
    }

    function ping(uint256 x) external returns (uint256) {
        if (mode == 6) Vault(msg.sender).totalShares();
        return x + mode;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        if (!inside && mode == 7) {
            inside = true;
            Vault(msg.sender).withdraw(amount);
            inside = false;
        }
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        return mode != 3;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        require(mode != 4, "no");
        if (mode == 5) {
            assembly {
                return(0, 0)
            }
        }
        if (inside && mode == 2) return false;
        if (!inside && mode == 1) {
            inside = true;
            Vault(msg.sender).deposit(amount / 2);
            inside = false;
        }
        if (!inside && mode == 2) {
            inside = true;
            try Vault(msg.sender).deposit(amount) {} catch {}
            inside = false;
        }
        balanceOf[from] -= amount;
        balanceOf[to] += amount;
        return mode != 3;
    }
}
