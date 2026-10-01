// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// The reference for examples/auction/Auction.bend: SimpleAuction from the
// Solidity documentation, with each send a call that reverts when it fails,
// a withdraw that sends also when nothing is owed, and status().
contract SimpleAuction {
    address payable public beneficiary;
    uint256 public auctionEndTime;
    address public highestBidder;
    uint256 public highestBid;
    mapping(address => uint256) public pendingReturns;
    bool public ended;

    event HighestBidIncreased(address bidder, uint256 amount);
    event AuctionEnded(address winner, uint256 amount);

    error AuctionAlreadyEnded();
    error BidNotHighEnough(uint256 highestBid);
    error AuctionNotYetEnded();
    error AuctionEndAlreadyCalled();

    constructor(uint256 biddingTime, address payable beneficiaryAddress) {
        beneficiary = beneficiaryAddress;
        auctionEndTime = block.timestamp + biddingTime;
    }

    function status() external view returns (address, uint256, bool) {
        return (highestBidder, highestBid, ended);
    }

    function bid() external payable {
        if (block.timestamp > auctionEndTime) revert AuctionAlreadyEnded();
        if (msg.value <= highestBid) revert BidNotHighEnough(highestBid);
        if (highestBid != 0) pendingReturns[highestBidder] += highestBid;
        highestBidder = msg.sender;
        highestBid = msg.value;
        emit HighestBidIncreased(msg.sender, msg.value);
    }

    function withdraw() external {
        uint256 amount = pendingReturns[msg.sender];
        pendingReturns[msg.sender] = 0;
        (bool ok,) = msg.sender.call{value: amount}("");
        if (!ok) revert();
    }

    function auctionEnd() external {
        if (block.timestamp < auctionEndTime) revert AuctionNotYetEnded();
        if (ended) revert AuctionEndAlreadyCalled();
        ended = true;
        emit AuctionEnded(highestBidder, highestBid);
        (bool ok,) = beneficiary.call{value: highestBid}("");
        if (!ok) revert();
    }
}

interface IAuction {
    function bid() external payable;
    function withdraw() external;
}

// A bidder that can misbehave when it gets ether back. 0: accept. 1:
// revert. 2: withdraw again, once. 3: bid again with the ether, once. It
// ignores a failure of the call again.
contract Bidder {
    IAuction public auction;
    uint256 public mode;
    bool private inside;

    constructor(IAuction a) {
        auction = a;
    }

    function setMode(uint256 m) external {
        mode = m;
    }

    function bid() external payable {
        auction.bid{value: msg.value}();
    }

    function withdraw() external {
        auction.withdraw();
    }

    receive() external payable {
        if (msg.sender != address(auction) || inside) return;
        require(mode != 1, "no");
        inside = true;
        if (mode == 2) try auction.withdraw() {} catch {}
        if (mode == 3) try auction.bid{value: msg.value}() {} catch {}
        inside = false;
    }
}
