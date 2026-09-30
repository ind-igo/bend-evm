import Base
import ../../../src/Evm.bend as Evm
import ./program.bend as Program
import ./LAWS.bend as Laws

def Laws.poke(storage, who, limit, logs, world, target, h):
  %h : {Bool.pick(Evm.Outcome<Unit>, _, Laws.poked(storage, who, limit, logs, world, target), Evm.Raise{Program.Reentrancy()})
    == Laws.poked(storage, who, limit, logs, world, target) : Evm.Outcome<Unit>}
  {==}

def Laws.reentered(storage, who, limit, logs, world, target, h):
  %h : {Bool.pick(Evm.Outcome<Unit>, _, Laws.poked(storage, who, limit, logs, world, target), Evm.Raise{Program.Reentrancy()})
    == Evm.Raise{Program.Reentrancy()} : Evm.Outcome<Unit>}
  {==}
