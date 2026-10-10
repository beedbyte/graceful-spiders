import K95Rooted
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let own : Array Name := #[`Boundary,`Amalgamation,`Certificates,`Interfaces,`Recurrence,`Shell,`PathGraph,`Residual,`Graft,`Identification,`SpiderTheorem,`SecondRecurrence,`SecondShell,`SecondSpider,`ThirdRecurrence,`ThirdShell,`ThirdSpider,`VariableGadget,`VariableCore,`VariableInterval,`VariableIdentification,`VariableSpider,`FiniteAlphaTransfer,`K23Packets,`TaggedDecode,`Q24Arrays,`Q24Graft,`Q24Positions,`Q24Family,`Q24B4Graft,`Q24Terminal,`K71Catalog0,`K71Catalog1,`K71Catalog2,`K71Catalog3,`K71Catalog4,`Q54Arrays,`Q54Certificates,`Q54Actual,`K71CatalogActual,`Q24B4Positions,`Q24MixFamily,`Q24Seed5Mix,`K71Boundary,`K71Tip,`K71Full,`RootedGraft,`RootedInjective,`Q24Rooted,`K95Catalog0,`K95Catalog1,`K95Catalog2,`K95Catalog3,`K95Catalog4,`K95Catalog5,`K95Catalog6,`K95Catalog7,`K95Catalog8,`K95Rooted]
  let allowed : Array Name := #[`propext,`Classical.choice,`Quot.sound]
  for (name,info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!
      if own.contains origin then
        match info with
        | .thmInfo _ =>
          let axioms ← collectAxioms name
          if axioms.any (fun a => !allowed.contains a) then
            throwError "Nonstandard axiom closure: {name}: {axioms.toList}"
          logInfo m!"CLOSURE|{name}|{origin}|{axioms.toList}"
        | .axiomInfo _ => throwError "Added project axiom declaration: {name}"
        | _ => pure ()
#print axioms GracefulBoundary.K95Rooted.packet_extreme
#print axioms GracefulBoundary.K95Rooted.catalog_extreme
#print axioms GracefulBoundary.K95Rooted.interior
