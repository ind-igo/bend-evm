import Base
import ../../src/Evm.bend as Evm

# An open auction, after SimpleAuction in the Solidity documentation. Bids
# are ether, and they end at a time that the constructor sets. A bidder who
# is outbid takes the ether back with withdraw. When the time is over,
# auctionEnd sends the highest bid to the beneficiary.
#
# There is no lock. Each function writes its state before it sends ether,
# and LAWS.bend proves that the send is its last step.
#
# Not as in the documentation: a send that fails reverts, as there are no
# low-level calls with a success flag yet, and withdraw sends to the caller
# also when it is owed nothing.

# Storage, in the order of the Solidity contract.
def BENEFICIARY() -> Nat:
  0n

def END() -> Nat:
  1n

def BIDDER() -> Nat:
  2n

def BID() -> Nat:
  3n

def PENDING() -> Nat:
  4n

def ENDED() -> Nat:
  5n

def HighestBidIncreased(bidder: Evm.Address, amount: Nat) -> Evm.Log:
  Evm.Log{"HighestBidIncreased", [], [bidder, amount]}

def AuctionEnded(winner: Evm.Address, amount: Nat) -> Evm.Log:
  Evm.Log{"AuctionEnded", [], [winner, amount]}

def AuctionAlreadyEnded() -> Evm.Error:
  Evm.Error{"AuctionAlreadyEnded", []}

def BidNotHighEnough(highestBid: Nat) -> Evm.Error:
  Evm.Error{"BidNotHighEnough", [highestBid]}

def AuctionNotYetEnded() -> Evm.Error:
  Evm.Error{"AuctionNotYetEnded", []}

def AuctionEndAlreadyCalled() -> Evm.Error:
  Evm.Error{"AuctionEndAlreadyCalled", []}

# The results of status.
def Status(highestBidder: Evm.Address, highestBid: Nat, ended: Evm.Boolean) -> Evm.Values:
  Evm.Values{[highestBidder, highestBid, ended]}

# The auction ends biddingTime seconds after it starts.
def init(+biddingTime: Nat, +beneficiaryAddress: Evm.Address) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    Evm.sstore(BENEFICIARY(), beneficiaryAddress)
    now : Nat <- Evm.timestamp()
    end : Nat <- Evm.add(now, biddingTime)
    Evm.sstore(END(), end)

def beneficiary() -> Evm.Contract(Evm.Address):
  Evm.sload(BENEFICIARY())

def auctionEndTime() -> Evm.Contract(Nat):
  Evm.sload(END())

def highestBidder() -> Evm.Contract(Evm.Address):
  Evm.sload(BIDDER())

def highestBid() -> Evm.Contract(Nat):
  Evm.sload(BID())

def pendingReturns(who: Evm.Address) -> Evm.Contract(Nat):
  Evm.load(PENDING(), who)

def ended() -> Evm.Contract(Evm.Boolean):
  Evm.sload(ENDED())

def status() -> Evm.Contract(Evm.Values):
  do Evm.Contract<Evm.Values>:
    bidder : Nat <- Evm.sload(BIDDER())
    bid : Nat <- Evm.sload(BID())
    over : Nat <- Evm.sload(ENDED())
    Evm.Contract.pure(Evm.Values, Status(bidder, bid, over))

# The caller becomes the highest bidder.
def lead(+who: Nat, +amount: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    Evm.sstore(BIDDER(), who)
    Evm.sstore(BID(), amount)
    Evm.emit(HighestBidIncreased(who, amount))

# The highest bidder is outbid, and can withdraw its bid.
def outbid(+who: Nat, +amount: Nat, +high: Nat) -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +bidder : Nat <- Evm.sload(BIDDER())
    owed : Nat <- Evm.load(PENDING(), bidder)
    sum : Nat <- Evm.add(owed, high)
    Evm.store(PENDING(), bidder, sum)
    lead(who, amount)

# A bid of the ether sent, before the end, and above the highest bid. The
# bidder it outbids can withdraw that bid.
def bid() -> Evm.Payable(Unit):
  do Evm.Contract<Unit>:
    now : Nat <- Evm.timestamp()
    end : Nat <- Evm.sload(END())
    Evm.ensure(Bool.not(Nat.is_lt(end, now)), AuctionAlreadyEnded())
    +who : Nat <- Evm.caller()
    +amount : Nat <- Evm.callvalue()
    +high : Nat <- Evm.sload(BID())
    Evm.ensure(Nat.is_lt(high, amount), BidNotHighEnough(high))
    Evm.branch(Unit, Nat.is_eq(high, 0n), lead(who, amount), outbid(who, amount, high))

# Sends the caller the bids it was outbid on.
def withdraw() -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    +who : Nat <- Evm.caller()
    amount : Nat <- Evm.load(PENDING(), who)
    Evm.store(PENDING(), who, 0n)
    Evm.pay(who, amount)

# Ends the auction once, after its end, and sends the highest bid to the
# beneficiary.
def auctionEnd() -> Evm.Contract(Unit):
  do Evm.Contract<Unit>:
    now : Nat <- Evm.timestamp()
    end : Nat <- Evm.sload(END())
    Evm.ensure(Bool.not(Nat.is_lt(now, end)), AuctionNotYetEnded())
    over : Nat <- Evm.sload(ENDED())
    Evm.ensure(Nat.is_eq(over, 0n), AuctionEndAlreadyCalled())
    Evm.sstore(ENDED(), 1n)
    +winner : Nat <- Evm.sload(BIDDER())
    +amount : Nat <- Evm.sload(BID())
    Evm.emit(AuctionEnded(winner, amount))
    to : Nat <- Evm.sload(BENEFICIARY())
    Evm.pay(to, amount)
