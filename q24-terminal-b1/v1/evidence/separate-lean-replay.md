# Independent copied-source Lean replay: q24 terminal B1

Status: **GO for the pinned Lean package and stated scope.** Private formal QA only. This does not upgrade priority or claim external review.

## Frozen inputs and isolated replay

- Author report `research-audits/graceful-q24-zero-order-formal-2026-10-10-a/report.md`: SHA-256 `5938f32ddc195cf59ef3f98074adf906c3b49d534937203277af2fc37b933bd1`.
- Author manifest `manifest.json`: SHA-256 `34dc5fecc2b007d14aa870abbbca3964ead91c7b7f9d76c315a2396902dacfe1`.
- Source index `SOURCE-SHA256SUMS.txt`: SHA-256 `c55f3f4af89434b2ab9439d5391237834b4f767a81a19daab3b26123a47db66d`; all 34 Lean source files were independently checked and copied byte-for-byte.
- The build used an empty `fresh-objects` directory, Lean 4.34.0, `-DwarningAsError=true`, `LEAN_PATH` set only to that directory, and `LEAN_SRC_PATH` unset. All 34 modules compiled and produced 34 fresh OLEANs. No author OLEANs or author object paths were imported.
- Executable SHA-256: `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`.
- Replay evidence: `build-result.json`, `queries/TerminalQuery.log`, and `control-results.json`.

## Verified theorem interfaces

The fresh query confirms:

- `GracefulBoundary.Q24Terminal.terminal_actual (t n m) (ht : 1 ≤ t) (hn : 2 ≤ n) (a : Fin n)` returns both `P20Q24.DepthZero n m (23+24*t) (20+22*t) a` and `P20Q24.DepthZero n m (23+24*t) (21+22*t) a`.
- `P20Q24.DepthZero` expands to a witness `f : SpiderVertex n m k → Nat` with `Graceful (spiderGraph n m k) (n*k+m) f` and zero at the actual named vertex `.arm a ⟨d-1,...⟩`. The two pair components have independent witnesses, so this is separate zero-labelings for each target. The statement includes arbitrary `m≥0` and every selected arm `a`.
- The generic `generic_source` theorem accepts any `P20Q24.State k z c` with `k=2*p+3`; it produces a `GenericPathCertificate (p+12)` for the extended path, the decoded maximum at index `z+1`, and zero at index `z+2`. Its premise is not restricted to the particular P20 orbit.
- Six concrete named-vertex instances compiled: both depths for `(t,n,m)=(1,2,0)`, both for `(1,2,1)`, and both for `(5,3,2)`, with selected arms explicitly instantiated.

All 18 new theorem declarations in the terminal module had fresh `#print axioms` checks. Every closure uses only `[propext, Classical.choice, Quot.sound]` or a subset. The terminal source contains no `axiom`, `sorry`, `admit`, or `native_decide`.

## Effective semantic controls

Six Lean controls failed because `decide` proved the stated proposition false, not due to syntax, missing imports, or unknown names:

- wrong B-gadget entry;
- wrong high-zero position;
- wrong midpoint label;
- a false repeated-state/iteration position;
- omission of the complement at the raw maximum;
- wrong terminal offset.

Each source and complete diagnostic log is under `controls/` and pinned in the package index.

## Scope and trust boundary

This replay verifies the frozen source package using the Lean kernel and pinned Lean executable. It does not establish literature priority or external/peer review. The author report marks priority of the exact terminal adapter **UNKNOWN**; this replay leaves that status unchanged. No public write was made.
