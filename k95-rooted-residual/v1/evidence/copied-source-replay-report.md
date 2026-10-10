# Independent full copied-source Lean replay: k95 arbitrary rooted residual

10 October 2026. **Independent copied-source formal GO for the exact interior theorem.** Private additive evidence; no publication or priority claim. No predecessor source or object bytes were changed.

## Exact theorem checked

The main declaration is `GracefulBoundary.K95Rooted.interior`. Its supplied residual graph is `H : IndexedGraph W F`, with an actual root `r : W`, labeling `g : W -> Nat`, edge bound `Q : Nat`, and a physical depth `d : Nat`. It requires `Rooted71.ConventionalGraceful H Q g`, `g r=0`, and `1<=d` and `d<=94`. The conclusion is a conjunction of two separate `Q24Rooted.ZeroAt H r Q 46` assertions at the actual path vertices `95-d` and `95+d`.

Each `ZeroAt` contains its own existential labeling of `graftGraph (pathGraph 190) H (Q24Rooted.center 46) r`, injective vertex labels in `0..190+Q`, a bijective edge-weight inventory `1..190+Q`, and zero at the stated `graftEmbed` vertex. The midpoint index95 is identified exactly with the actual residual root, leaving all H vertices/edges and adding two separately named95-edge paths. The two existential witnesses may differ. There is no alpha, tree, connectedness or onto-vertex premise on H. The finite-band injection/bijection and existence of r imply that the indexed vertex/edge types are finite, without requiring a separate `Fintype` binder.

Our independently written `ReplayAudit.exact_interior` restates this in expanded concrete `Fin 191`, `pathGraph 190`, midpoint95 and bound190+Q form, rather than only accepting a printed theorem name. It compiles using the independently rebuilt principal theorem. The printed main type is also captured in `build-logs/AuditPositive.log`.

The theorem makes no claim about new depth95/tips or any old residual vertex. Its result is conventional gracefulness, not the project's stronger vertex-band onto predicate. A separate supplied root-max labeling could be normalized by complementing H, but arbitrary prescribed nonzero roots are not part of this exact theorem. No zero-rotatability conclusion for all vertices of an arbitrary H is inferred.

## Frozen inputs and independent import closure

Author report SHA256: `e8ec1733d50564cf5599767a59fecc17f332ead05395438c9c71d9ba2d0e05a6`.

Author source index SHA256: `6371f4c80715cc8aacdf6a34bd4259740e9844265e004f5985d25eda04d9889d`.

The source index and every listed original source byte were checked before copying. We independently followed module imports from `K95Rooted`, resolving only names from four explicitly pinned source indexes and checking that shared module names have identical hashes. The exact transitive project closure contains **59 modules**, including the RootedInjective -> RootedGraft -> K71Full dependency and the necessary q24/k95 catalogs. It is not a replay of only the two incremental author sources. `copy-bindings.json` records every origin, input index, import, module order and copied hash; `COPIED-SOURCE-SHA256SUMS.txt` binds all59 copied files. The three predecessor indexes are:

- k95 full formal: `e25a837ba4f27f6c7a1770e0f2ed245077f2eb282d6a8128c6d1b477c2a94d5d`.
- k71 rooted residual formal: `45b2c193ce997f0d150dd90be66c13dff6daf38f666671dd887d177d3d775eba`.
- q24 terminal formal: `c55f3f4af89434b2ab9439d5391237834b4f767a81a19daab3b26123a47db66d`.

The author checks and mutants listed in its source index were hash-verified as bytes but were not executed or used as test implementation. No author build/generation/literal checker scripts were read or run. All replay commands, type assertions, positive instances and semantic mutants were written separately in this packet. Author captured results and OLEANs were not used to determine success.

## Fresh compiler execution and trust boundary

Compiler: Lean4.34.0, x86_64-w64-windows-gnu, commit293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release. Executable SHA256 `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`.

The isolated `objects` directory was empty before the first project module. Every copied project module compiled sequentially with `-DwarningAsError=true`, producing fresh objects. The only explicitly supplied `LEAN_PATH` is this new object directory. No author/predecessor OLEAN, server/private sidecar or build directory is in that search path. Standard-library objects come from the pinned compiler installation; these are the explicit toolchain trust boundary, not independently rebuilt source in this packet. The compiler executable is hash-pinned; no full standard-library source/object inventory is claimed.

All59 project builds exit0. Each module's source provenance, duration, log and generated object hash are captured in `build-summary.json`; every compiler-produced object/sidecar is additionally bound in `object-inventory.json` and the complete package inventory. Checks import only these fresh objects and the toolchain standard library. We do not require object-byte equality with the author's differently located build; source equality and fresh kernel-checked compilation are the claim.

## Axioms and complete module-origin inventory

`WholeClosure.lean` traverses the loaded environment and selects theorem declarations by originating module, using the explicit59-module closure list. Thus selection does not rely on a public namespace or omit private declarations merely because of their names. It independently collects each theorem's transitive axioms and rejects any closure beyond `propext`, `Classical.choice`, `Quot.sound`. An axiom declaration originating in a project module is also rejected. The toolchain's own unrelated theorem declarations are outside the59-module inventory.

The independent result is **2239 theorem closures**, all standard-only; `axiom-inventory.json` is the declaration-by-declaration inventory and `module-closure-counts.json` records module totals. All three principal declarations (`packet_extreme`, `catalog_extreme`, `interior`) have exactly the standard closure recorded in `principal-closures.json`. No `sorryAx`, added project axiom, `admit` or `native_decide` is accepted. This inventory is for the imported project theorem environment, while the successful separately written assertions additionally demonstrate the precise type and named cases. No claim of independently verified underlying foundational consistency is made.

## Non-onto topology and positive instances

Our explicit triangle has vertices/edges `Fin 3`, actual edges0--1,1--2,2--0 and labels0,1,3. We prove conventionally graceful weights1,2,3 and root label0, and separately prove it is not onto0..3 (label2 has no vertex). This nonbipartite, non-tree residual meets exactly the principal premise. `triangle_all_depths` instantiates both arms for every physical d in1..94. There are also188 individually named triangle side/depth instances and8 singleton/one-edge endpoint-depth instances, **196 concrete target assertions** total. The singleton Q0 and edge Q1 correspond to the two-arm n2,m0 and n2,m1 boundary residual shapes, without relying on a spider-only transfer type.

All positive checks pass under warnings-as-errors. No triangle is upgraded to full vertex-band gracefulness: only conventional injection and full edge weights are asserted. There are190+3 output vertices and193 edges in the triangle graft; a full onto0..193 vertex labeling would require194 distinct vertices, so that stronger conclusion is not supported.

## Four effective semantic mutants

- `WrongRoot`: keep a conventional one-edge residual but choose its label1 root and attempt to supply `g r=0`. The intended root-zero proof is rejected. A possible different labeling or normalized residual is not ruled out.
- `Tip95`: attempt the principal theorem at d95. Its exact upper-bound proof95<=94 is rejected; this is an interface limit, not a proof the actual tip cannot receive zero under another construction.
- `OldResidualVertex`: substitute an old H root vertex for the actual newly added arm target. The result fails by target/type mismatch. The underlying graph might admit another old-vertex-zero labeling; none is inferred here.
- `FalseOnto`: promote the triangle's conventional output witness to the stronger `Graceful` vertex-band predicate. Its type is rejected at that proposed strengthening.

All four fail with the intended semantic errors using the same freshly rebuilt imports and a successful baseline. Missing modules, unknown identifiers, missing object files and syntax failures are expressly excluded as acceptable negative controls. Exact diagnostic logs are preserved. These mutants check theorem scope, not graph nonexistence.

## Freeze and remaining boundaries

Independent copied-source formal GO is limited to the exact k95 two-new-arm interior theorem above. Mathematical priority, literature subsumption and any publication decision remain separate. The alpha high-side shift, translation, complement and identified-root graft are established operations; this replay makes no operation-novelty claim and performs no new literature audit. No public files or frozen predecessor bytes were edited.

The complete recursive manifest/root index includes sources, objects and sidecars, logs, independent checks, inventories, scripts and this report. Only exact root `manifest.json` and root `SHA256SUMS.txt` have their required self-exceptions. Nested source indexes are included rather than excluded by basename. Original input source bindings are checked again at freeze. This is a full replay of the59-source import closure, not a complete inventory/rebuild of all four predecessor packages or the standard library.

To reproduce, create a new workspace from the independent scripts and pinned inputs; run `replay.py prepare`, `replay.py build`, `make_checks.py`, and `run_checks.py` sequentially. Never regenerate in this frozen directory. `verify_final.py` is read-only and verifies this current inventory, copied sources, original source pins, objects and closure records. No further author edits are authorized by this freeze.
