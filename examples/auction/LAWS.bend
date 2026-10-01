import Base
import ../../src/Evm.bend as Evm
import ./Auction.bend as Auction

# The laws of the auction (Auction.bend). Each gives every outcome from any
# state. Storage is newest first, so new slots shadow old ones.

def stored(storage: List<&2, Evm.Slot>, slot: Nat) -> Nat:
  Evm.lookup(storage, Evm.Plain{slot})

def owed(storage: List<&2, Evm.Slot>, who: Nat) -> Nat:
  Evm.lookup(storage, Evm.Mapped{Evm.Plain{4n}, who})

def now(facts: List<&2, Evm.Fact>) -> Nat:
  Evm.fact.of(facts, Evm.Timestamp{}, [])

# The constructor sets the end to the block's time and the bidding time.
law init:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +biddingTime: Nat
  for +beneficiary: Nat
  {Evm.run(Unit, Auction.init(biddingTime, beneficiary), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Evm.time.of(world), biddingTime), limit),
      Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{1n}, Nat.add(Evm.time.of(world), biddingTime)}
        <> Evm.Slot{Evm.Plain{0n}, beneficiary} <> storage, who, limit, logs, world}},
      Evm.Revert{}) : Evm.Outcome<Unit>}

# The sender leads with the value sent.
def led(+storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>, +world: Evm.World,
  +value: Nat) -> Evm.Outcome<Unit>:
  Evm.Ok{Unit{}, Evm.State{Evm.Slot{Evm.Plain{3n}, value} <> Evm.Slot{Evm.Plain{2n}, who} <> storage, who, limit,
    Evm.Log{"HighestBidIncreased", [], [who, value]} <> logs, world}}

# The bid it outbids, which its bidder can withdraw.
def credited(+storage: List<&2, Evm.Slot>) -> List<&2, Evm.Slot>:
  Evm.Slot{Evm.Mapped{Evm.Plain{4n}, stored(storage, 2n)}, Nat.add(owed(storage, stored(storage, 2n)), stored(storage, 3n))}
    <> storage

# A bid reverts at or after the end with AuctionAlreadyEnded, and unless
# it is above the highest bid with BidNotHighEnough. Else the sender leads,
# and the bidder it outbids is owed that bid. The value sent is the first
# reading, which callvalue uses up. auctionEnd raises before the end, so no
# bid comes after an end.
law bid:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +facts: List<&2, Evm.Fact>
  for +value: Nat
  for +readings: List<&2, Nat>
  for +self: Nat
  for +hashes: List<&2, Evm.Hashed>
  for +signers: List<&2, Evm.Signed>
  for +answers: List<&2, Evm.Answer>
  {Evm.run(Unit, Auction.bid(), Evm.State{storage, who, limit, logs,
      Evm.World{facts, value <> readings, self, hashes, signers, answers}})
    == Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(now(facts), stored(storage, 1n)),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(stored(storage, 3n), value),
        Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(stored(storage, 3n), 0n),
          led(storage, who, limit, logs, Evm.World{facts, readings, self, hashes, signers, answers}, value),
          Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(owed(storage, stored(storage, 2n)), stored(storage, 3n)), limit),
            led(credited(storage), who, limit, logs, Evm.World{facts, readings, self, hashes, signers, answers}, value),
            Evm.Revert{})),
        Evm.Raise{Auction.BidNotHighEnough(stored(storage, 3n))}),
      Evm.Raise{Auction.AuctionAlreadyEnded()}) : Evm.Outcome<Unit>}

# A withdrawal sets what the sender is owed to zero, and only then sends
# it, as its last step: a receiver that calls back to withdraw again is
# owed nothing.
law withdraw:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  {Evm.run(Unit, Auction.withdraw(), Evm.State{storage, who, limit, logs, world})
    == Evm.Calling{Evm.Pay{who, owed(storage, who)},
      Evm.State{Evm.Slot{Evm.Mapped{Evm.Plain{4n}, who}, 0n} <> storage, who, limit, logs, world},
      _ => t => Evm.Ok{Unit{}, t}} : Evm.Outcome<Unit>}

# The end reverts before the end time with AuctionNotYetEnded, and after
# the first end with AuctionEndAlreadyCalled. Else it marks the auction
# ended and logs, and only then sends the highest bid to the beneficiary,
# as its last step.
law auctionEnd:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  {Evm.run(Unit, Auction.auctionEnd(), Evm.State{storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Bool.not(Nat.is_lt(Evm.time.of(world), stored(storage, 1n))),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_eq(stored(storage, 5n), 0n),
        Evm.Calling{Evm.Pay{stored(storage, 0n), stored(storage, 3n)},
          Evm.State{Evm.Slot{Evm.Plain{5n}, 1n} <> storage, who, limit,
            Evm.Log{"AuctionEnded", [], [stored(storage, 2n), stored(storage, 3n)]} <> logs, world},
          _ => t => Evm.Ok{Unit{}, t}},
        Evm.Raise{Auction.AuctionEndAlreadyCalled()}),
      Evm.Raise{Auction.AuctionNotYetEnded()}) : Evm.Outcome<Unit>}

# The beneficiary is paid once: after an end, every end reverts, also one
# from a callback while the first end sends the bid.
law once:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  {Evm.run(Unit, Auction.auctionEnd(), Evm.State{Evm.Slot{Evm.Plain{5n}, 1n} <> storage, who, limit, logs, world})
    == Bool.pick(Evm.Outcome<Unit>, Bool.not(Nat.is_lt(Evm.time.of(world), stored(storage, 1n))),
      Evm.Raise{Auction.AuctionEndAlreadyCalled()},
      Evm.Raise{Auction.AuctionNotYetEnded()}) : Evm.Outcome<Unit>}
