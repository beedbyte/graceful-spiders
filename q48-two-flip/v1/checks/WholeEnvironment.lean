import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Boundary
import Amalgamation
import Certificates
import Interfaces
import Recurrence
import Shell
import PathGraph
import Residual
import Graft
import Identification
import SpiderTheorem
import SecondRecurrence
import SecondShell
import SecondSpider
import ThirdRecurrence
import ThirdShell
import ThirdSpider
import VariableGadget
import VariableCore
import VariableInterval
import VariableIdentification
import VariableSpider
import FiniteAlphaTransfer
import K23Packets
import TaggedDecode
import Q24Arrays
import Q24Graft
import Q24Positions
import Q24Family
import Q24B4Graft
import Q24B4Positions
import Q24MixFamily
import Q24Seed5Mix
import Q48Graft
import Q48Positions
import Q48Family
set_option maxHeartbeats 0
run_cmd do
  let env ← Lean.getEnv
  let modules : Array String := #["Boundary","Amalgamation","Certificates","Interfaces","Recurrence","Shell","PathGraph","Residual","Graft","Identification","SpiderTheorem","SecondRecurrence","SecondShell","SecondSpider","ThirdRecurrence","ThirdShell","ThirdSpider","VariableGadget","VariableCore","VariableInterval","VariableIdentification","VariableSpider","FiniteAlphaTransfer","K23Packets","TaggedDecode","Q24Arrays","Q24Graft","Q24Positions","Q24Family","Q24B4Graft","Q24B4Positions","Q24MixFamily","Q24Seed5Mix","Q48Graft","Q48Positions","Q48Family"]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := (env.header.moduleNames[idx.toNat]!).toString
      if modules.contains modName then
        if info.isAxiom then throwError "package-local axiom: {name}"
        if info.isTheorem then
          let axs ← Lean.collectAxioms name
          for ax in axs do
            unless #["propext", "Classical.choice", "Quot.sound"].contains ax.toString do
              throwError "unexpected axiom {ax} in {name}"
          count := count+1
          Lean.logInfo m!"THEOREM|{name}|{modName}|{axs}"
  Lean.logInfo m!"ALL_PACKAGE_THEOREMS={count}; STANDARD_ONLY"
#check GracefulBoundary.Q48Flip.selected_actual
#check GracefulBoundary.Q48Flip.terminal_actual
#check GracefulBoundary.Q48Flip.terminal_certificate
#print axioms GracefulBoundary.Q48Flip.selected_actual
#print axioms GracefulBoundary.Q48Flip.terminal_actual
#print GracefulBoundary.P20Q24.State
#print GracefulBoundary.Graceful
#print GracefulBoundary.SpiderVertex
#print GracefulBoundary.spiderGraph
