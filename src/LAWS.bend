import Base
import ./Evm.bend as Evm
import ./ir.bend as IR
import ./yul.bend as Yul

# The lowering keeps the meaning of every IR command, for each output kind,
# environment, continuation and state, in the Yul model of yul.bend. That
# model uses the EVM's modular arithmetic, so this covers the real overflow
# check. Evm.run is the case where k returns Ok.
law preserves:
  for +cmd: IR.Cmd
  for +out: IR.Output
  for +env: List<&2, IR.Binding>
  for R: Data
  for k: IR.value(out) -> Evm.State -> Evm.Outcome<R>
  for +s: Evm.State
  {Yul.exec(Yul.lower(cmd, out), out, env, R, k, s) == IR.run(cmd, out, env, R, k, s) : Evm.Outcome<R>}
