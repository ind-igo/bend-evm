// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

interface Notes {
    function note(uint256 id, string calldata text, bytes calldata data) external;
}

// The reference for tests/fixtures/bytes in Solidity.
contract Reference {
    event Note(uint256 indexed id, string text, bytes data);

    error Refused(uint256 code, string reason);

    function note(uint256 id, string calldata text, bytes calldata data) external {
        emit Note(id, text, data);
    }

    function echo(bytes calldata data) external pure returns (bytes memory, uint256) {
        return (data, data.length);
    }

    function size(bytes calldata data) external pure returns (uint256) {
        return data.length;
    }

    function refuse(uint256 code, string calldata reason) external pure {
        if (code != 0) revert Refused(code, reason);
    }

    function hash(bytes calldata data) external pure returns (bytes32) {
        return keccak256(data);
    }

    function forward(address target, bytes calldata data) external returns (uint256) {
        return Receiver(target).onData(msg.sender, data);
    }
}

// The target of forward. It calls back note with the bytes it got, and
// returns their length plus one.
contract Receiver {
    function onData(address sender, bytes calldata data) external returns (uint256) {
        Notes(msg.sender).note(uint256(uint160(sender)), "back", data);
        return data.length + 1;
    }
}
