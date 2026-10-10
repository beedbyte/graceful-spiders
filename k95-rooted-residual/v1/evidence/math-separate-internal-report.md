# Separate mathematical audit: k95 arms over a rooted graceful graph

10 October 2026. Private additive audit. **Mathematical GO for the exact conditional interior-arm statement.** No claim for either new tip or an arbitrary old residual vertex is obtained here. No new Lean verification, public write, external review or priority claim.

## Independence and frozen inputs

The vertex/weight-band argument was reconstructed from the task statement before opening the author's report, and the checker below was implemented separately. However, the initial19-line report read exposed both its scope and its short transfer paragraph. This audit is therefore **not fully blind to the author's prose**. No author `check.py` or `results.json` was opened, copied, imported or executed. The author manifest was read only as an index; report/manifest byte hashes are input bindings. This limitation was disclosed to root before checking.

Author scope report: `research-audits/graceful-k95-rooted-residual-transfer-2026-10-10-a/report.md`, SHA-256 `0704b6f204b44f294509c67c9be24c9e96ca5284806604b5049e4fb8b94c6e2d`.

The mathematical source inputs are the public fixed-k95 package's [exact catalog](https://github.com/beedbyte/graceful-spiders/blob/a6cd0889a354a50b9ecc80bbd3162972639d63e3/fixed-k95/v1/data/lean-catalog.json), SHA-256 `882f8914da746eec0f7b3e9ba7e460fed1022b8f66148db94b27b6e8a1392975`, and its [payload index](https://github.com/beedbyte/graceful-spiders/blob/a6cd0889a354a50b9ecc80bbd3162972639d63e3/fixed-k95/v1/SHA256SUMS.txt), SHA-256 `97d4c9a638723dfb06ed424ca6020ebb7f39688d4e5f4e9b1dd8affe7ed7e8ee`. Both local source files equal the corresponding committed Git blobs at a6cd0889a354a50b9ecc80bbd3162972639d63e3. This audit checked those local committed bytes, not a fresh network readback. `source-reference.json` records the exact links and hashes. Every file under the public package index is hash-checked; none of its code is executed by this implementation.

## Exact theorem

Let H be a finite undirected graph with Q edges, a specified vertex r, and a conventional graceful labeling g:V(H)→{0,…,Q}. Here conventional means **injective** vertex labels and a bijection from edges to weights1..Q under absolute difference; surjectivity of g onto0..Q is not assumed. Require g(r)=0.

Adjoin two disjoint named paths of95 edges each, identifying only their initial vertices with r. Retain every old vertex and old edge. For either new arm a∈{0,1} and every physical depth d∈{1,…,94}, the resulting graph admits a target-dependent conventional graceful labeling with zero at the actual new vertex(a,d).

The resulting edge count is Q+190 and the vertex-label range is0..Q+190. The hypothesis is about a supplied zero labeling at the specified root, not merely the existence of an unrelated graceful labeling of H. If g(r)=Q instead, complementing g first gives this hypothesis. An arbitrary interior root label does not suffice by this argument.

There is no target statement here for depth95 or old vertices of H. A rejected out-of-scope request in the checker is an interface control, not a proof of nonexistence of another labeling.

## 1. Independent finite path certificate check

For each d1..94, the public catalog selects a191-entry word P. The new checker directly verifies labels0..190 once each, differences1..190 once each, P[95]=94, every edge crossing cut94, and P[95−d]∈{0,190}. It checks both extreme metadata and the selected component. There are51 distinct words and94 target rows. Reversing P preserves its midpoint/cut and puts the selected extreme at95+d.

These are complete finite certificates. They are the precise source premise needed here; the general residual result is not inferred merely from the published all-vertex fixed-spider theorem. No solver or author checker is used.

## 2. Exact topology and label injection

Use old vertex names disjoint from `(new,a,d)`, a∈{0,1},1≤d≤95. Edges are exactly E(H), the two root-to-depth1 edges, and consecutive-depth edges within each new arm. Thus |V(G)|=|V(H)|+190 and |E(G)|=Q+190. This remains true for a cyclic or disconnected residual; the operation adds no extra old vertex, suppresses no vertex and adds no short hub leaf.

Choose the source orientation putting the desired extreme on the selected arm. For each old vertex v use F(v)=94+g(v). On a new source vertex with source value x use x when x≤94, and x+Q when x≥95. The root identification is consistent because both source midpoint and F(r) are94.

The three nonoverlapping label parts are:

- new low vertices: exactly0..93 (the only source vertex with94 is the identified root);
- old vertices: the injective subset94+g(V(H)) of94..Q+94;
- new high vertices: exactlyQ+95..Q+190.

Consequently F is injective and lies in0..Q+190. No step uses that g fills its allowed interval. The image misses exactly `{94+j : j∈{0,…,Q}\g(V(H))}` before complementation. In particular full-band surjectivity holds **if and only if** g is onto0..Q; the number of missing labels is Q+1−|V(H)|. A residual tree with Q+1 vertices is a sufficient special case, not a requirement of the conventional theorem.

## 3. Exact weight partition and selected zero

An old edge uv has weight |94+g(u)−94−g(v)|=|g(u)−g(v)|, so old weights are1..Q once. On every new edge the source endpoints satisfy low≤94<high. Its weight becomes `(high+Q)−low=Q+(high−low)`. The190 path differences1..190 therefore become Q+1..Q+190 exactly. The two edge sets are disjoint and exhaust1..Q+190.

For a source zero the target remains0. A source maximum190 becomes N=Q+190. Replacing **every** old and new label by N−F(v) preserves injectivity, range and all absolute differences and puts zero at that target. Complementing only the new arms is not justified and is rejected by a control. Each target gets a separate labeling.

These partition equalities prove the theorem for all finite H,Q satisfying the hypothesis, without extrapolating the finite graph tests. Q=0 is included: injectivity into{0} and the named root force the singleton residual, and the output is the source path itself.

## 4. The non-onto triangle and an additional boundary check

Take H=K3 with root label0 and other labels1,3. Q=3 and the edge weights are1,2,3. This is conventionally graceful, but label2 is absent. The graft has193 vertices and193 edges, with injective labels in0..193. For a direct-zero source (depth2), the unique missing label is96=94+2. For a maximum-derived source (depth1), whole-graph complement makes the missing label97=193−96. Both new arms and every requested interior depth are checked on this triangle.

Thus claiming onto0..193 would be false:194 allowed labels cannot all be used by193 vertices. The ordinary conventional statement passes, while the deliberately strengthened onto mutation fails. The example does not refute the author's scoped statement, which explicitly uses conventional gracefulness.

As an additional check, add an isolated old vertex labeled2 to that triangle. This disconnected residual is onto despite containing a cycle; its graft is onto as well. This confirms that the exact criterion is residual surjectivity, not a claimed converse saying only trees can be onto.

## 5. Finite tests and effective controls

`check.py` uses only the Python standard library and reads no author code/results. For Q1..5 it chooses one unordered label pair of each difference1..Q from0..Q, retains the incident named vertices and root0, and checks the resulting residual premise. This yields1!+2!+3!+4!+5!=153 named edge-assignment cases. With the Q0 singleton and two explicit triangle variants there are156 residual cases; these are not claimed pairwise nonisomorphic.

Every case is transferred at all94 interior depths on both named arms: **29,328 full named graph labelings and5,708,620 actual edge checks**. There are12,220 onto and17,108 non-onto output cases. Actual incidence and vertex identities are built separately from the labeling function. All old vertices and edges are included, not just the path halves. Finite tests support falsification of the implementation; the universal proof is the preceding partition argument.

Eighteen effective mutants reject: false onto for the triangle; missing source depth; wrong midpoint; missing old root or vertex; wrong high shift or alpha boundary; missing, partial, or inappropriate complement; wrong named arm or physical depth; a tip or old vertex passed to the interior-only interface; a nonzero designated root; invalid old edge inventory; deleted attachment edge; and an incorrect arm incidence. These controls are ordinary explicit exceptions, not Python asserts. Normal and `-O` results are byte-identical in `normal.json`/`optimized.json`.

## Verdict and limits

**GO for the conventional-graceful, root-zero residual transfer to both new95-arms at every interior depth1..94.** The stronger onto property is conditional precisely on the old labeling being onto. **No result for the new tips or arbitrary old residual vertices**, and no assertion that every specified root of a graceful graph admits zero.

This is the familiar alpha-label band/amalgamation mechanism applied to the pinned k95 path inventory; no new primitive operation or worldwide priority is claimed. The public Lean source supplies the frozen path certificates and fixed-spider results; this audit does not formalize the arbitrary-H conventional-graph theorem in Lean. The proof/checker are separate, but the exposed author prose means the review is not described as completely blind. No external specialist or peer review is asserted, and no public files were changed.
