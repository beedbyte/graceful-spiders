import K119Through118
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let own : Array Name := #[`Boundary,`Amalgamation,`Certificates,`Interfaces,`Recurrence,`Shell,`PathGraph,`Residual,`Graft,`Identification,`SpiderTheorem,`SecondRecurrence,`SecondShell,`SecondSpider,`ThirdRecurrence,`ThirdShell,`ThirdSpider,`VariableGadget,`VariableCore,`VariableInterval,`VariableIdentification,`VariableSpider,`FiniteAlphaTransfer,`K23Packets,`TaggedDecode,`H1Append,`H1Concrete,`H1ConcreteLookup,`H1ConcreteShift,`H1ConcreteFinal,`Q24Arrays,`Q24Graft,`Q24Positions,`Q24Family,`Q24B4Graft,`Q24Terminal,`K71Catalog0,`K71Catalog1,`K71Catalog2,`K71Catalog3,`K71Catalog4,`Q54Arrays,`Q54Certificates,`Q54Actual,`K71CatalogActual,`Q24B4Positions,`Q24MixFamily,`Q24Seed5Mix,`K71Boundary,`K71Tip,`K71Full,`RootedGraft,`RootedInjective,`Q24Rooted,`TerminalNormalized,`K119Catalog0,`K119Catalog1,`K119Catalog2,`K119Catalog3,`K119Catalog4,`K119Catalog5,`K119Catalog6,`K119Rooted,`TerminalSeed56,`K119Through114,`TerminalSeed34,`TerminalSeed12,`K119Through118]
  let allowed : Array Name := #[`propext,`Classical.choice,`Quot.sound]
  for (name,info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!
      if own.contains origin then
        match info with
        | .thmInfo _ =>
          let axioms ← collectAxioms name
          if axioms.any (fun a => !allowed.contains a) then
            throwError "Nonstandard closure: {name}: {axioms.toList}"
          logInfo m!"CLOSURE|{name}|{origin}|{axioms.toList}"
        | .axiomInfo _ => throwError "Added project axiom: {name}"
        | _ => pure ()
#print axioms GracefulBoundary.TerminalSeed34.seed_input
#print axioms GracefulBoundary.TerminalSeed34.seed_not_old_state
#print axioms GracefulBoundary.TerminalSeed34.path_certificate
#print axioms GracefulBoundary.TerminalSeed34.extreme_positions
#print axioms GracefulBoundary.TerminalSeed34.rooted_expanded
#print axioms GracefulBoundary.TerminalSeed12.seed_input
#print axioms GracefulBoundary.TerminalSeed12.seed_not_old_state
#print axioms GracefulBoundary.TerminalSeed12.path_certificate
#print axioms GracefulBoundary.TerminalSeed12.extreme_positions
#print axioms GracefulBoundary.TerminalSeed12.rooted_expanded
#print axioms GracefulBoundary.K119Through118.expanded
