import Base
import ./Evm.bend as Evm
import ./ir.bend as IR
import ./yul.bend as Yul

import ./calls.bend as Calls

# The lowering keeps the meaning of every IR command, for each output kind,
# environment, continuation and state, in the Yul model of yul.bend. That
# model uses the EVM's modular arithmetic, so this covers the real overflow
# check. The two runs are compared under every list of answers and
# callbacks (calls.bend): the left one runs callbacks through the lowered
# entries, as the compiled contract does, and the right one through their
# IR. With no answers, calls.bend's drive is the outcome itself unless a
# call is left unanswered; Evm.run is the case where k returns Ok.
law preserves:
  for +entries: List<&2, Calls.Entry>
  for +steps: List<&2, Calls.Step>
  for +cmd: IR.Cmd
  for +out: IR.Output
  for +env: List<&2, IR.Binding>
  for R: Data
  for k: IR.value(out) -> Evm.State -> Evm.Outcome<R>
  for +s: Evm.State
  for +open: Bool
  {Calls.drive(Calls.Lowered{}, entries, steps, R, open, Yul.exec(Yul.lower(cmd, out), out, env, R, k, s))
    == Calls.drive(Calls.Model{}, entries, steps, R, open, IR.run(cmd, out, env, R, k, s)) : Evm.Outcome<R>}

# Callbacks run the same through the lowered entries as through their IR,
# from any outcome. So a law about Calls.drive with the Model, such as an
# invariant across callbacks, holds for the compiled entries too.
law callbacks:
  for +entries: List<&2, Calls.Entry>
  for +steps: List<&2, Calls.Step>
  for A: Data
  for +open: Bool
  for o: Evm.Outcome<A>
  {Calls.drive(Calls.Lowered{}, entries, steps, A, open, o) == Calls.drive(Calls.Model{}, entries, steps, A, open, o) : Evm.Outcome<A>}

# A value of the environment that is fixed in a transaction uses up no
# reading, so a second read of it gives the same word.
law fixed:
  for +e: Evm.Env
  for +s: Evm.State
  for +h: {True{} == Evm.fixed(e) : Bool}
  {Evm.sensed(e, s) == s : Evm.State}

# A callback's bytes argument decodes to the bytes that the ABI encoded,
# when its words are as many as its length needs. So the model of callbacks
# reads bytes as the encoder writes them.
law decodes:
  for +n: Nat
  for +ws: List<&2, Nat>
  for +h: {List.length(&2, Nat, ws) == Nat.div(Nat.add(n, 31n), 32n) : Nat}
  {Calls.decode(32n, Evm.abi([Evm.Dynamic{Evm.Bytes{n, ws}}])) == Some{Evm.Bytes{n, ws}} : Maybe<&2, Evm.Bytes>}
