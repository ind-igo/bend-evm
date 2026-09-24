import Base
import ./Evm.bend as Evm
import ./ir.bend as IR
import ./yul.bend as Yul

# The lowering keeps the meaning of every IR command, for each output kind,
# environment and state, in the Yul model of yul.bend. That model uses the
# EVM's modular arithmetic, so this covers the real overflow check.
law preserves:
  for +cmd: IR.Cmd
  for +out: IR.Output
  for +env: List<&2, IR.Binding>
  for +s: Evm.State
  {Yul.exec(Yul.lower(cmd, out), out, env, s) == IR.run(cmd, out, env, s) : Evm.Outcome<IR.value(out)>}
