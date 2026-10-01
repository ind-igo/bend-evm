import Base
import ../../src/Evm.bend as Evm
import ./Auction.bend as Auction
import ./LAWS.bend as Laws

def Laws.init(storage, who, limit, logs, world, biddingTime, beneficiary):
  {==}

# A run stops at the branch on the highest bid, which is not known, so the
# lemma takes the branch's condition as c and matches on it.
def bid.go(c: Bool, +storage: List<&2, Evm.Slot>, +who: Nat, +limit: Nat, +logs: List<&2, Evm.Log>,
  +facts: List<&2, Evm.Fact>, +value: Nat, +world: Evm.World) ->
  {Bool.pick(Evm.Outcome<Unit>, Bool.not(Nat.is_lt(Laws.stored(storage, 1n), Laws.now(facts))),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Laws.stored(storage, 3n), value),
        Evm.branch(Unit, c, Auction.lead(who, value), Auction.outbid(who, value, Laws.stored(storage, 3n)))(Unit,
          x => t => Evm.Ok{x, t}, Evm.State{storage, who, limit, logs, world}),
        Evm.Raise{Auction.BidNotHighEnough(Laws.stored(storage, 3n))}),
      Evm.Raise{Auction.AuctionAlreadyEnded()})
    == Bool.pick(Evm.Outcome<Unit>, Bool.not(Nat.is_lt(Laws.stored(storage, 1n), Laws.now(facts))),
      Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Laws.stored(storage, 3n), value),
        Bool.pick(Evm.Outcome<Unit>, c,
          Laws.led(storage, who, limit, logs, world, value),
          Bool.pick(Evm.Outcome<Unit>, Nat.is_lt(Nat.add(Laws.owed(storage, Laws.stored(storage, 2n)), Laws.stored(storage, 3n)), limit),
            Laws.led(Laws.credited(storage), who, limit, logs, world, value),
            Evm.Revert{})),
        Evm.Raise{Auction.BidNotHighEnough(Laws.stored(storage, 3n))}),
      Evm.Raise{Auction.AuctionAlreadyEnded()}) : Evm.Outcome<Unit>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.bid(storage, who, limit, logs, facts, value, readings, self, hashes, signers, answers):
  bid.go(Nat.is_eq(Laws.stored(storage, 3n), 0n), storage, who, limit, logs, facts, value,
    Evm.World{facts, readings, self, hashes, signers, answers})

def Laws.withdraw(storage, who, limit, logs, world):
  {==}

def Laws.auctionEnd(storage, who, limit, logs, world):
  {==}

def Laws.once(storage, who, limit, logs, world):
  {==}
