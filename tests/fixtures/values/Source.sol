// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

// The contract that tests/fixtures/values calls.
contract Source {
    error Nope(uint256 code);

    function getReserves() external pure returns (uint256, uint256, uint256) {
        return (11, 22, 33);
    }

    function fail() external pure returns (uint256) {
        revert Nope(7);
    }
}
