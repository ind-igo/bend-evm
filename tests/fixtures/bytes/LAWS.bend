import Base
import ../../../src/Evm.bend as Evm
import ./program.bend as Program

# The laws of tests/fixtures/bytes: each bytes value goes on as the ABI
# encodes it.

# forward calls onData with the caller and the bytes, and returns its word.
law forward:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +target: Nat
  for +data: Evm.Bytes
  {Evm.run(Nat, Program.forward(target, data), Evm.State{storage, who, limit, logs, world})
    == Evm.Calling{Evm.Call{target, "onData", Evm.abi([Evm.Word{who}, Evm.Dynamic{data}])},
      Evm.State{storage, who, limit, logs, world}, x => t => Evm.Ok{x, t}} : Evm.Outcome<Nat>}

# echo returns the bytes and their length.
law echo:
  for +s: Evm.State
  for +data: Evm.Bytes
  {Evm.run(Evm.Values, Program.echo(data), s)
    == Evm.Ok{Evm.Values{Evm.abi([Evm.Dynamic{data}, Evm.Word{Evm.length(data)}])}, s} : Evm.Outcome<Evm.Values>}

# note logs the two texts after their offsets: the second starts after the
# first one's length word and words.
law note:
  for +storage: List<&2, Evm.Slot>
  for +who: Nat
  for +limit: Nat
  for +logs: List<&2, Evm.Log>
  for +world: Evm.World
  for +id: Nat
  for +n: Nat
  for +ws: List<&2, Nat>
  for +data: Evm.Bytes
  {Evm.run(Unit, Program.note(id, Evm.Bytes{n, ws}, data), Evm.State{storage, who, limit, logs, world})
    == Evm.Ok{Unit{}, Evm.State{storage, who, limit,
      Evm.Log{"Note", [id], 64n <> Nat.add(96n, Nat.mul(List.length(&2, Nat, ws), 32n)) <> n
        <> List.append(&2, Nat, ws, List.append(&2, Nat, Evm.tail(data), []))} <> logs, world}} : Evm.Outcome<Unit>}
