# Terminal-normalized seeds 3/4 and 1/2; fixed K119 interior 1–118

Frozen 2026-10-10T11:05:39.320043+00:00. **AUTHOR FORMAL GO** for the exact all-r families and fixed-K119 interior theorem below. This is a private additive formalization after separately frozen mathematical QA. A separate copied-source replay of this new68-source packet remains a later gate. It is not external review, public release, or a worldwide-priority claim.

## 1. Exact formal scope

For every r≥1 let K_r=30·4^r−1. The new `GracefulBoundary.TerminalSeed34.rooted_expanded` proves separate zero labelings at depths K_r−4 and K_r−3 on each of the two physically named new K_r-edge arms. `GracefulBoundary.TerminalSeed12.rooted_expanded` proves the corresponding statement at K_r−2 and K_r−1. Both quantify over arbitrary indexed H, supplied conventional graceful labeling g with edge span Q, and a specified root with g(root)=0. Q=0 is permitted. H need not be vertex-onto, connected, acyclic, or alpha-labeled.

The graph in each statement is exactly `graftGraph (pathGraph (2*K)) H ⟨K,...⟩ root`, on `GraftVertices (Fin (2*K+1)) W ⟨K,...⟩`. The two separate existential labelings have span2K+Q and zero at `graftEmbed ... ⟨K-d,...⟩` and `graftEmbed ... ⟨K+d,...⟩`. Their labeling functions may differ. The supplied root-zero premise is not a conclusion about the final root label.

The fixed-length principal is **`GracefulBoundary.K119Through118.expanded`**. For every such H,Q,g,root and every natural depth **1≤d≤118**, it proves the same two independent actual named-graph zero placements on the new119-edge arms. The graph has a238-edge path grafted at index119, plus all of H; the final edge span is238+Q. The companion `interior` exposes the equivalent `Q24Rooted.ZeroAt` propositions at exact indices119−d and119+d.

This is full coverage of the **interiors of the two newly attached arms** at K119. It does not zero old-H vertices, the shared root, new tips119, or multiple vertices simultaneously. It does not prove full interior coverage for every r>1, all odd arm lengths, or every vertex of an arbitrary mixed spider. The all-r statements are the specified four near-tip depths; old terminal-normalized families cover other near-tip pairs separately.

## 2. Exact literal and correction bindings

The independent mathematical QA report is `graceful-k119-terminal-k29-seeds-independent-2026-10-10-a/report.md`, SHA74ae0eee7c29d1c0042ba237ab2bdd86307788f9f7e7452d74310696356a1784. Its corrected source mapping is preserved exactly:

| New module | Source literal | SHA-256 | Original zero indices | Targets at K119 |
|---|---|---|---|---|
| TerminalSeed34 | graceful-k119-depth115-terminal-seed-2026-10-10-a/result.json | af466f84614f492debfd28a396af2cddcaf2a2547d6efaa4605dbd341e544cf6 | L0 at3, H0 at4 | 116,115 |
| TerminalSeed12 | graceful-k119-depth117-terminal-seed-2026-10-10-a/result.json | 0d8b0c0164b98fcd3e28ee7d95016cd43aa4d7355c9ad94ff0fe317ab4bf9e93 | L0 at1, H0 at2 | 118,117 |

Both original reports and authoritative correction addenda are pinned. Index4 addendum SHAd502660b55dedd36f71425b65b072f62804bdfa63f860eaf3d174ac57006b0f2; index2 addendum SHAba39f587ca51a0fbec4622757d808a53027f4a17fb8fbaef857c435a1849b5b3. Original malformed references/low-zero wording were not silently edited or reused as the corrected statement. The literal arrays in the new Lean files match the pinned JSON words exactly.

Each59-entry literal is kernel-certified by ordinary `decide` as `TerminalNormalized.Input 13 seed29`: length59, H offsets0..29, L offsets0..28, adjacent sums0..57, terminal28. Both inputs fail the old midpoint28 at index29 (actual values18 and21). The index1/2 seed happens to share the old H1 prefix, while index3/4 does not; neither proof assumes that prefix. Each module proves `seed_not_old_state` from the midpoint failure. No solver was run or made part of the formal trust boundary.

## 3. Generalized proof and exact composition

The frozen `TerminalNormalized.Input` has only length, high inventory, low inventory, adjacent sums and terminal fields. `family_input` preserves that weakened contract through the explicit concrete append for all iterations. `family_midpoint` supplies the newly positioned midpoint after each positive iteration. The all-parameter `H1Concrete.concrete_tail` theorem discharges the tail-inventory premise; no unproved `ConcreteTailInventory` assumption survives.

Both new modules adapt the frozen index5/6 theorem skeleton using the corrected literals and exact low/high indices. They use `family_lookup` to preserve original positions3/4 or1/2. `WholeTagged.whole_path_certificate` then establishes the full path permutation, complete edge differences, alpha cutK−1 and physical midpoint labelK−1. Closed arm length is proved asK=30·4^r−1. Odd-index source zeros are label0; even-index source zeros decode to2K. Generic rooted transfer and path reversal supply the two named arms. A maximum target requires whole-graft complement after its high labels are raised byQ; a low target remains zero directly.

The final fixed wrapper imports the **exact frozen** `K119Through114` module and performs the following exhaustive split:

| Depth interval | Discharged Lean source |
|---|---|
| 1–114 | K119Through114.interior |
| 115–116 | TerminalSeed34.rooted_both at r1 |
| 117–118 | TerminalSeed12.rooted_both at r1 |

Inside the predecessor,1..110 is K119Rooted,111/112 is the original terminal-normalized index7/8 family, and113/114 is TerminalSeed56. There is no unproved coverage-table premise. The final theorem quantifies over d and H and proves the actual graph result through this split. The fixed expansion carries every finite-index bound in Lean.

## 4. Frozen predecessor and fresh build

The65-source predecessor is `graceful-terminal-normalized-seed56-formal-2026-10-10-a`. Its report SHA7880991872e7168be32c6e855d2c99c9d913051047fe523a0870637a35265219; manifest SHA76e65e770e3d716bc16d0c18f4cbf911ff6de62fba33b345fcd08e14c8f0f0d9; source index SHAed7d0bed8e629395ecd8713673a47ab6cd749edc8a1b16a00d077bd0c08d9d9c. In particular K119Through114 source SHAd7596ee70ddebae13f7584b7846bf95393dcf1a4d1b67567f153583283e31140 and TerminalSeed56 source SHA15b390379a57aeef35bf4254b16ccd2d439c64d9210dbad54cef7e18610e8367 match the announced freeze.

This new package copied all65 sources byte-for-byte and added exactly3 modules. **All68 final sources compiled in a fresh warningAsError build into an initially empty object directory**, using source cwd and bare module filenames. No predecessor OLEAN was copied or imported. The complete topological import closure and toolchain are recorded. Lean executable4.34.0 SHAa8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2. The predecessor data/scripts/records were only read. All declared source and input hashes were reread after testing.

The derivation script records the exact frozen templates used for the two new seed modules and the fixed wrapper. This is code reuse and a new author formalization, not a claim of blind independent implementation. Its complete fresh build validates every imported source, but a separate copied-source replay of this successor remains pending.

## 5. Verification and countercontrols

The entire68-module project theorem census contains **2809** declarations, including generated/private helper theorems. Every axiom closure is contained in propext, Classical.choice, Quot.sound. The closure gate rejects any added project axiom or nonstandard theorem dependency. Exact source-specific principal closures and independent query helper closures are printed in the retained logs. Literal certification uses kernel `decide`, not `native_decide` or an external solver result.

**1072 concrete named Lean instances** were checked: all118 interior depths on both arms for singleton(Q0), one edge(Q1), non-onto triangle(Q3), and K4 plus isolated vertex(Q6), plus both new all-r families at r1..4 with all four residuals and both arms. The K4-plus-isolate labels0,1,4,6,2 give an explicit cyclic, disconnected, non-onto residual. Support proofs verify its edge weights1..6, failed onto condition, isolated vertex and triangle cycle. These samples corroborate the parametric proof and the exact graph/index conventions; they are not the source of the all-H/all-r quantifiers.

**16 effective semantic mutants** reject: tip119 and center0 being claimed by the interior theorem; wrong arm and offset; nonzero supplied root; r0; an outside family depth; treating r2 as full-interior coverage; wrong seed midpoint or coercion into old State; wrong extreme and new midpoint label; wrong closed length; an onto requirement; omitted whole-graft complement; and conflation of separate labelings. These rejected applications are not graph-impossibility claims. No missing-name/module error or resource exhaustion is counted as a successful mutant.

The first Python closure postprocessor used an unverified minimum of2900 declarations and stopped after the successful Lean audit. Inspection found a complete census of2809 theorems across all66 theorem-bearing modules; the two remaining modules only define arrays. The corrected gate checks exact count and module coverage. No Lean source or proof changed; initial check results and the development note are retained. The full final control run was repeated.

Own normal/optimized Python verifier outputs are byte-identical. The verifier checks68 source/object pairs,65 copied predecessor sources, exact mathematical literal identities and zero indices, input-midpoint failure, final proof/check results and all frozen input pins. It uses explicit exceptions, so `python -O` cannot suppress checks. Source and object indexes bind final bytes. No frozen predecessor was altered.

## 6. Status and limits

Correctness status here: **author formal GO** for the exact two new families and fixed-K119 interior1..118. Independent mathematical QA of the literals and transfer was already frozen before this formalization. The new source package still requires its separately assigned copied-source replay before any coordinated release. The older generic append and alpha/rooted graft are established operations; this task does not claim their invention. The previously pinned primary comparison identifies the append as older endpoint-matched concatenation plus alpha relabeling. Exact worldwide priority remains **UNKNOWN**; no fresh primary-literature search, human review or peer review is claimed.

There were no public, CMS, website, profile or GitHub writes. Every artifact is additive and private. New proof source hashes appear in the manifest and source index; final theorem types and failure diagnostics remain inspectable.

## Reproduction

For a separate replay, copy source/ and module-order.json to a new empty directory; compile each bare module filename in source cwd using Lean4.34.0, warningAsError, with only the fresh output directory on LEAN_PATH. Then copy checks/ and run Support, Positive, WholeClosure and the listed mutants against those newly built objects. Build/check scripts document the exact commands. To regenerate author source from frozen inputs, use prepare.py in a new empty sibling directory; never run it against this frozen package. Do not use shipped objects as a substitute for rebuilding sources.
