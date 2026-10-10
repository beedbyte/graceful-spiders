# Independent aggregate mathematical QA: fixed k=95

## Decision and exact scope

**Mathematical GO.** For every integer n>=2 and m>=0, each actual existing vertex of S(95^n,1^m) can separately receive zero in a graceful labeling. The graph has a named hub, n named arms of length 95, and m named original hub leaves. The assertion includes all named arms and all physical depths 1..95, the hub, and every original short leaf. A separate labeling is allowed for each target. This is neither one labeling with multiple zeros nor a theorem for arbitrary odd lengths or a parametric family.

The frozen author coverage-union report is bound at SHA256 `e613621a97f439c00672e69a2cf261885f0b463697bdeeaaa781999749a72d17`; its manifest is `8766d164d0f66ec3795559f663310d3251a725a86fbc0c69aabdaadd48f4ea74`. This audit supplies a separately implemented complete finite path catalog and an explicit universal graph transfer. It is more than a checksum comparison.

No Lean compiler or author objects are used in this mathematical audit. The separately frozen full-k95 Lean author report and manifest are bound in `status-binding.json` as status evidence only. Their copied-source replay is a separate pending gate. `ledger.json` preserves the earlier pre-freeze formal-status snapshot; this paragraph and the status binding record the later author freeze without rewriting that snapshot. The second depth-92 audit was pending at the last root confirmation; this report does not claim its completion. Our direct depth-92 certificate check and universal transfer are complete.

## Independent finite source checks

`audit.py` uses only the Python standard library. It imports or executes no author or predecessor checker. The current aggregate author checker was not read. An older `check_witness.py` was read to inspect the q9 literal/specification interface and is pinned explicitly; the present implementation is separate, but is not blind to that mathematical framework or the existing transfer lemmas.

Every accepted source word P has length 191, labels exactly 0..190, adjacent differences exactly 1..190, midpoint P[95]=94, and every edge crosses the cut 94. These checks are full inventories, rather than SAT status assertions. A canonical word hash identifies each literal in `catalog.json`; provenance records exact input file, row pointer, and construction.

The catalog has 51 distinct words covering every depth 1..94. There were 168 full path-contract checks, including overlapping witnesses. The independent extraction proceeds as follows:

| Depths | Independently checked source route |
|---|---|
| 1 | Explicit two-arm midpoint-alpha formula |
| 2..71 | p=46 compatible cores, reflection where needed, and the H3 shell |
| 72/73 | Old p=37 bank row 886, q9 P4 insertion, reflection, H3 shell |
| 74..77 | Old p=37 bank row 882, q9 P4/P2 insertion, reflection, H3 shell |
| 77..86 | Both q24 initial seeds, all B2/B4 orders of length 3 |
| 87 | Two normal B2 steps followed by the separately verified terminal B1 adapter |
| 88..92 | Individually pinned P191 certificates; CP87 also checked as an overlap |
| 93/94 | State-10 seed at k=23 followed by the unconditional H1 tail |
| 95 | Elementary actual-graph tip extension; no P191 premise needed |

For 74..77 the separately reconstructed words are exactly equal to the earlier saved literals. For 72/73 our source is an alternative to the later Lean author's independently constructed source. The P20 seed alone covers 79..86 at t=3; the z=5 additional seed supplies 77/78. The union is 77..86. A control rejects treating P20 alone as that larger interval.

The six separately checked CP sources have (zero depth, maximum depth): CP87 (86,87), CP88 (88,87), CP89 (88,89), CP90 (90,89), CP91 (90,91), CP92 (92,91). The terminal B1 source gives 87 by whole-graph complementation. It is used once after compatible normal steps, without asserting that its output satisfies the normal recursive window.

The actual D8 graph route is `GapDepth -> Q11Depth -> ReverseDepth`, giving radius 73 at k=95. The directly bound graph source and D8 copied-source replay supply its actual-graph premise. A half-length arithmetic lemma alone would not establish that graph premise. Our finite catalog additionally verifies the needed fixed-length sources independently. Similarly, an earlier finite-only CP audit is not silently upgraded to a universal graph theorem: the next section supplies the missing universal transfer explicitly.

## Universal actual-graph proof

Write each arm vertex as (a,d), with 0<=a<n and physical depth 1<=d<=95. Original leaves are (leaf,j), 0<=j<m. Edges are hub--(a,1), (a,d-1)--(a,d) for d>=2, and hub--(leaf,j). Thus every named vertex and edge is explicit; m=0 has no leaf obligations.

First construct a hub-zero residual with h arms. For arm rank 0<=i<h set

```
R(h,i,d) = 95(h-i) - (d-1)/2   when d is odd,
           95i + d/2           when d is even.
```

The hub has label 0 and the m leaves have labels 95h+1,...,95h+m. Division in these formulas is exact on the stated parity. The even-depth labels on arm i form [95i+1,95i+47]. The odd-depth labels on arm h-1-i form [95i+48,95(i+1)]. Consequently all arm labels partition 1..95h. This includes h=0, when only the hub and original leaves remain.

Root-edge weights are the multiples 95,190,...,95h. Each arm's internal weights have the form |95(h-2i)-v|, 1<=v<=94. If h-2i>0 they form the block immediately below 95(h-2i); otherwise they form the block immediately above 95(2i-h). The resulting block indices h-2i-1 (positive case) and 2i-h (other case) cover 0..h-1 exactly: one part has one parity and the other the opposite parity. Together with the root edges these weights partition 1..95h. Leaf weights fill 95h+1..95h+m. This proves the residual formula for every h,m, including the singleton and one-leaf cases.

Now fix a target arm a and an independently certified P191 word whose extreme occurs at the required distance from its midpoint. Choose any distinct partner b; n>=2 guarantees it exists. Assign the two physical halves of P to a and b, orienting them so the target extreme lies on a. Set h=n-2, Q=95h+m, and N=95n+m=190+Q. Keep source labels <=94 fixed and increase every source label >94 by Q. Assign the remaining named arms and original leaves by the above residual, translated by 94; identify its hub with the path midpoint.

The non-hub vertex-label bands are 0..93 from the source lows, 95..94+Q from the residual, and 95+Q..190+Q from the source highs; the hub is 94. They partition 0..N with no collision. Because every source edge crosses 94, its weight increases by Q, giving Q+1..N. Residual weights are 1..Q. The exact target graph consists of the two original 95-edge arms, all n-2 remaining named 95-edge arms, and exactly the m original leaves. Thus both full inventories and the topology hold for all n,m and every selected arm, including n=2,m=0/1.

If the target source extreme is zero, it remains zero. If it is 190, it becomes N; replace every label x on the whole graph by N-x. This preserves the full label and weight inventories and makes the target zero. Complementing only the two source arms is not valid and is rejected by a control.

This transfer applies in particular to the old p37/q9 sources for 74..77. Those sources have no hidden n>=3 or m>0 restriction. The finite source certificate and this universal proof are distinct gates, both checked here.

## Endpoints, hub and original short leaves

The hub-zero residual formula with h=n proves the hub case directly. For an existing original leaf j, remove only that named leaf, use the residual labeling of the remaining graph, add j with new maximum label N at the hub zero, and complement the whole graph. The edge added has weight N and the selected original leaf becomes zero. This applies to every j<m; for m=0 the statement is vacuous, rather than an invented leaf target.

For the selected long-arm tip, remove that arm, preserving the hub, all other named arms, and all original leaves. Label the remaining graph with hub zero. Grow the removed arm one vertex at a time at the current zero: in a q-edge gracefully labeled graph with current zero v, attach the next vertex at v with label q+1, then complement every label by q+1. The old weights remain 1..q, the new weight is q+1, the old v becomes the new maximum, and the new vertex is zero. Repeat exactly 95 times. The attachment point advances along the new arm and creates the required chain, without creating extra hub leaves. Its tip is zero. A final whole-graph complement makes the predecessor at depth 94 zero. This also proves the boundary cases when n=2,m=0/1.

Depth 1 uses the explicitly checked alpha source. Its left-arm physical labels are 190-(d-1)/2 for odd d and d/2-1 for even d; the right-arm labels are 95+(d-1)/2 for odd d and 94-d/2 for even d. This source satisfies the same midpoint and crossing contract, so the universal transfer applies.

The case split is therefore complete: hub; original leaf j<m; or a named arm vertex with 1<=d<=95. For arm depths choose 1 by the boundary source, 2..73 by the D8/independent catalog, 74..76 by old p37/q9, 77..86 by the combined q24 sources, 87 by the terminal source or CP overlap, 88..92 by their pinned certificates, 93 by H1, and 94/95 by the boundary constructions. All depth-index conversions use physical depth d, corresponding to Lean's depth-minus-one d-1.

## Checks, controls and trust boundary

Normal and optimized Python outputs are byte-identical. The actual named-graph implementation checks all targets for (n,m)=(2,0),(2,1),(3,2),(4,1): 1,053 graphs and 301,160 edges. Eleven additional independent predecessor-tip constructions also pass. These finite checks falsify implementation errors; the universal assertions rest on the partition proof above, not extrapolation from those graph counts.

Eleven controls reject omissions of old 74..76, H1 depth 93 and depth 92; the enlarged P20-only range; a phantom m=0 leaf; omission of an actual m=1 leaf; a wrong selected arm; a wrong physical depth; complementation of an already-zero CP92 target; partial rather than whole-graph complementation; and unsupported terminal self-iteration. Details are in `normal.json`.

The 35 direct computational/source bindings appear in `input-pins.json`. Three later Lean-author status files are separately bound in `status-binding.json`; they are not mathematical inputs or compiler verification. This is exact input binding, not a full inventory or rebuild of all predecessor packages. The current package's own recursive inventory is complete, including nested index files; only the exact root index excludes itself, and the manifest excludes its own exact root path and the exact root index. Python's executable hash is recorded; this does not inventory the entire installed runtime.

This packet is a private mathematical QA, with no new Lean module, axiom closure or solver claim. The existing operations and transfer methods have prior-source context. Worldwide priority of the particular fixed-k95 result is UNKNOWN; no independent literature search or external review is claimed. Publication is not authorized by this freeze. Historical source and published all-even package bytes are untouched. The new full-k95 Lean author's build and its independent replay remain separately attributable gates.

Reproduction: run `python -B audit.py` and `python -O -B audit.py` with the pinned executable, capturing outputs separately; those commands regenerate the catalog/ledger/dependencies in a fresh copy. `verify_final.py` performs the read-only inventory and direct-input checks on the frozen packet. Do not rerun generating commands in the immutable original.
