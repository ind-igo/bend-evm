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
