// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

interface IGuarded {
    function poke(address target) external;
    function locked() external view returns (uint256);
}

// The target of poke. In ping, it reads the lock and calls poke again, and
// keeps what it saw.
contract Hook {
    uint256 public seen;
    bytes public error;

    function ping() external returns (uint256) {
        seen = IGuarded(msg.sender).locked();
        try IGuarded(msg.sender).poke(address(this)) {
            error = "none";
        } catch (bytes memory data) {
            error = data;
        }
        return 7;
    }
}
