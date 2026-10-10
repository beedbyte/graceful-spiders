# Independent copied-source Lean replay: fixed k=95

Decision: **GO** for the frozen fixed-k95 Lean package and theorem scope below. This is private internal QA, not a public release or an external/peer review. The historical priority status remains **UNKNOWN**.

## Pinned inputs and isolated build

- Frozen author report `research-audits/graceful-k95-full-formal-2026-10-10-a/report.md`: SHA-256 `bd565d980e75e9c7670e2cc96f5ac6ec4bc8f00fe6a41cd5292fd6fc1850d53d`.
- Frozen author manifest: SHA-256 `3264bf57460ea55a94c0d1f091b6875cfa2cbead3e889e098252ce2f9c3a4b69`.
- Frozen source index `SOURCE-SHA256SUMS.txt`: SHA-256 `e25a837ba4f27f6c7a1770e0f2ed245077f2eb282d6a8128c6d1b477c2a94d5d`; it lists 35 Lean sources. Every indexed source was independently checked and copied byte-for-byte into `copied-source/`.
- Lean 4.34.0 compiled all 35 copied modules with `-DwarningAsError=true`. `fresh-objects/` was empty before the build; `LEAN_PATH` pointed only to this new directory and `LEAN_SRC_PATH` was unset. The build produced 35 fresh OLEANs. No author objects or author logs were used as build inputs.
- Lean executable SHA-256: `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`.
- Build evidence: `build-result.json`. The independent query and its full output are `queries/K95Query.lean` and `queries/K95Query.log`.

## Exact theorem types and axiom audit

The fresh query prints the principal declarations:

```lean
theorem GracefulBoundary.K95Full.all_vertices
    (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 95) :
    ∃ f : SpiderVertex n m 95 → Nat,
      Graceful (spiderGraph n m 95) (95*n+m) f ∧ f v = 0

theorem GracefulBoundary.K95Full.unique_zero
    (n m : Nat) (hn : 2 ≤ n) (v : SpiderVertex n m 95) :
    ∃ f : SpiderVertex n m 95 → Nat,
      Graceful (spiderGraph n m 95) (95*n+m) f ∧
      ∀ w, f w = 0 ↔ w = v
```

These quantify over the actual indexed vertex type, including center, all named arm/depth pairs, and existing leaves. The only theorem inputs are `n`, `m`, `hn : 2≤n`, and the supplied actual vertex; the target is the full `spiderGraph n m 95`, with all original leaves included. `unique_zero` is checked as an exact sole-zero strengthening.

Fresh `#print axioms` checks covered `K95Full.interior`, `arm_depth_zero`, `all_vertices`, `unique_zero`, `K95Boundary.center_zero`, `leaf_zero`, `K95Tip.tips_prescribed_zero`, and the generic `FiniteAlpha.prescribed_zero`. Each closure uses only `[propext, Classical.choice, Quot.sound]`. All 35 source files were also scanned for code-level `axiom`, `sorry`, `admit`, `sorryAx`, `opaque`, `unsafe`, `implemented_by`, `ofReduceBool`, and `native_decide`; none occurred. `Interfaces.lean` contains named *definitions* of open proposition obligations, but the printed full theorem types have no such premise, the principal axiom closures contain no custom axiom, and the main wrapper is built from the proved finite catalog and graph transfer.

## Concrete actual-vertex checks and negative controls

Thirteen independent examples compiled from the fresh objects: eleven direct `all_vertices` applications and two `unique_zero` applications. They cover the hub, the first arm vertex, interior depths 74, 87, and 92, depths 94 and the physical tip 95, short leaves at `m=1` and `m=2`, selected arms 0/1/2, and both `n=2,m=0` and `n=2,m=1`, plus `n=3,m=2`. The two unique-zero cases target the arm tip with `m=0` and an actual leaf with `m=1`.

Eight independent semantic controls were rejected: three false literal-certificate mutations (zero depth, maximum depth, midpoint label), phantom leaf at `m=0`, invalid application at `n=1`, omitted leaf contribution from the edge count, out-of-range named arm, and wrong arm length. The three literal mutations fail because `decide` evaluates the changed proposition as false. The other five fail at their intended type/index/false-premise mismatch; none failed for syntax or missing imports. Sources and diagnostics are under `controls/` and indexed below. The `n=1` failure checks only that the theorem interface requires `n≥2`; it is not a claim that the path graph is ungraceful.

## Separate mathematical QA status

The independent aggregate mathematical QA is separately frozen at `research-audits/graceful-k95-coverage-independent-2026-10-10-a/report.md`, SHA-256 `2951a634ac3c94e1fe21e48e0591dcc5bfd921fc1028f5911c0d7970e39ec287`. It reports GO for the same all-n,m/all-actual-vertex scope. That report is status context only; it is not imported or used as a Lean premise in this replay.

## Trust boundary and limits

This verifies the 35 pinned source files with the Lean 4.34.0 kernel and standard library. It does not certify the compiler itself, establish literature priority, or upgrade the private result into external review. Scope is fixed `k=95`; no neighboring-length or unbounded-family theorem is asserted. No public write was made.
