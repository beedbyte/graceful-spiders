# Index5/6 terminal seed: unbounded rooted family and K119 depths1–114

Private additive Lean author packet, 10 October2026. **Author formal GO** for the two exact theorems below. This record reports the author build and its controls, not a separate copied-source replay or external specialist review. No public release was made. Earlier mathematical/formal packets remain unchanged.

## Exact results

1. `GracefulBoundary.TerminalSeed56.rooted_expanded`: for every natural r>=1, K=30*4^r-1, arbitrary indexed graph H with supplied conventional graceful labeling g into0..Q, and supplied root with g(root)=0, attach two new K-edge arms. For either d=K-6 or d=K-5, each named arm separately admits a whole-graph conventional graceful labeling with zero at that depth. No onto condition on g, connectedness or tree premise occurs. The physical indices are K-d and K+d in the new2K-edge path, whose midpoint indexK is identified with the old root.

2. `GracefulBoundary.K119Through114.expanded`: for that same arbitrary supplied root-zero H, attach two119-edge arms. Every depth d with1<=d<=114 on either new arm admits its own whole-graph graceful labeling with zero at the named vertex. The expanded graph type uses Fin239, pathGraph238, shared index119, total238+Q edges and targets119-d/119+d.

These are separate labelings, not a common labeling with multiple zeros. Neither theorem supplies tips, arbitrary old-H vertices, all odd arm lengths or full K119 interior coverage. In particular this package supplies no depth115–118 theorem. It does not promise that the resulting root remains labeled zero. Worldwide exact priority remains UNKNOWN.

## Exact seed and reused interface

The input literal is taken from the frozen author result `graceful-k119-depth113-terminal-seed-2026-10-10-a/result.json`, SHA5512bb02ab3061ca948c9ee49d90e663b987c7e8ec3285c86c8b51724bc58394. Its checker hash8325ed3150e433637d77be4453b591bd17880a662ae16e5bfbb94816f27bf2d5 is bound as provenance; that Python program was not imported as a formal proof. The formal `seed_input` uses ordinary kernel `decide` to check the exact59-tag word against `TerminalNormalized.Input 13`. Its high zero is at physical index6 and low zero at5. Its midpoint is19, not28, and `seed_not_old_state` proves it fails the older stronger H1 State.

The prior additive generalized interface is copied byte-for-byte from `graceful-terminal-normalized-append-formal-2026-10-10-a`, whose source index is a2465ba3f70f65086604e112ce1daa81c8eb72222909fa010072d11c58de3dca and report SHA12c02016f2c10b1576e5c0467398b532b12ccf9f88b6e0893afcfd3d4e922e8c. No new assumption is added to that interface and no old source is changed.

The weakened input contains exactly length, high/low permutations, adjacent-sum permutation and terminal normalization. `family_input`, `family_midpoint` and `family_lookup` from the copied interface use the unconditional concrete-tail inventory theorem. They establish the entire iteration for the new seed. `path_certificate` gives the full decoded midpoint-alpha path for every positive iteration; `extreme_positions` preserves exact indices5/6. The output midpoint indexK has low labelK-1; index5 is label0 and index6 is label2K. The inherited arbitrary-H graft and whole-graph complement/reversal place zero at depthsK-5/K-6 on either arm. `arm_length_closed` proves K=30*4^r-1. No tail premise, finite-run extrapolation or solver assumption is hidden in the final theorem.

## Exact fixed-K119 composition

`K119Through114.interior` splits the interval explicitly:

| Depths | Imported/proved source |
|---|---|
|1..110|Frozen `K119Rooted.interior`, already separately replayed in report d2052524d5d4a94c96df2974b6e37b79888a556dd229ba368c13d7b920d31705|
|111/112|Frozen `TerminalNormalized.rooted_both` at r1, from the index7/8 seed|
|113/114|New `TerminalSeed56.rooted_both` at r1, from this index5/6 seed|

The displayed disjunctions are kernel-checked and depend on the inclusive upper bound114. No extrapolation from a source catalog count is used. The old theorem is copied with unchanged bytes; the composition is a new module.

## Build and test record

The exact transitive import tree has65 source modules:63 byte-identical copied predecessors, plus `TerminalSeed56.lean` and `K119Through114.lean`. All were compiled from an initially empty object directory with Lean4.34.0 and warningAsError. No predecessor/author OLEAN was copied. `module-order.json`, the source index and per-module final build records pin those exact final bytes. The Lean compiler executable hash is recorded in compiler.json.

The complete theorem closure audit includes 2733 project declarations (including generated/private names) and 247 query declarations, 2980 in total. Every closure uses only propext, Classical.choice and Quot.sound. Static scans reject sorry, admit, added axioms, native_decide and implemented_by proof shortcuts.

The query suite has240 actual named triangle-target declarations: all228 combinations of K119 depth1..114 and either arm, plus12 family examples at r1,2,3 for its two depths and two arms. Four family examples repeat K119 targets deliberately; the larger family checks add8 distinct higher-length targets. The old residual triangle has labels0,1,3 and is formally conventional graceful but not onto0..3, so the examples test the intended nononto interface rather than an accidental stronger premise.

Fifteen effective semantic mutants reject zero iterations, wrong old-source zero/midpoint, nonzero residual root, incorrect closed length/recurrence, wrong new midpoint, missing complement, coercion to the old stronger State, onto substitution, reversed terminal, swapped named arm, depth115, tip119 and falsely claiming depth112 from this specific seed. Their rejection is evidence against those exact uses of the interface, not a graph nonexistence assertion. Normal and optimized Python gate outputs are identical; they verify all source origins and frozen input pins, exact import closure, final build bytes, query/log pins, literal equality and the printed expanded theorem types.

## Prior art, formal trust and remaining gates

The append operation is older endpoint-matched concatenation, precisely identified in the prior source comparison with [Hicks–Ollis–Schmitt, proof of Lemma4.5](https://community.middlebury.edu/~jschmitt/papers/HicksOllisSchmitt2018.pdf) plus alpha relabeling, and [Adamaszek2006 Lemma1](https://arxiv.org/pdf/math/0608513). Generic root-zero/alpha grafting is also prior work. This task instantiates the positional source and composes exact formal coverage; it does not establish operational novelty or worldwide priority. The older primary comparison report c69f93cf3f1fd96648cf8877f741b8202f034371303ae0ef60e33ddd4186bd59 remains the bound for those attribution statements. No fresh global literature survey was performed.

The Lean kernel, standard axioms, exact predecessor definitions and compiler/runtime form the trust boundary. The ordinary literal check is kernel reduction, not native_decide or imported solver evidence. The new formal author result still calls for separate copied-source replay and the separately assigned mathematical QA. This report does not retrospectively rewrite any pending-status sentence in its historical inputs.

For reproduction in a fresh directory, copy source/, queries/, module-order.json, mutants.json, build.py and check_queries.py; begin without objects. With the pinned Lean4.34.0 executable run `python -X utf8 build.py`, then `python -X utf8 check_queries.py`. Existing private objects are build evidence, not required proof inputs. The workspace verifier additionally checks the exact original source records; immutable manifest and SHA index bind the package. No external contact or public write occurred.
