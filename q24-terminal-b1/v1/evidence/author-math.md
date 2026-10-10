# A terminal q24 graft with reversed extreme order

Private additive author mathematics, 10 October 2026. **Author mathematical GO** for the exact universal source transfer and actual-spider statement below. Separate post-freeze mathematical QA and Lean reconstruction remain pending. No public write or external contact. Historical priority is **UNKNOWN**.

## 1. Exact theorem and gain

For every integer t≥1, let k=23+24t. For all n≥2,m≥0 and each selected named long arm a of the actual S(k^n,1^m), separate graceful labelings put zero at the vertices of depths

    20+22t and 21+22t.

The actual vertices are hub c, (arm,a,d), 0≤a<n and1≤d≤k, and m original hub leaves. Label inventories are0..nk+m and actual edge weights1..nk+m. No additional leaf or suppressed degree-two vertex is involved. In particular n=2,m=0/1 is included.

The upper target is the first depth beyond the previous q24 upper bound U_t=20+22t. For t≥5, combining this theorem with the already established D8/q24 prefix gives every selected-arm depth

    1≤d≤21+22t=(11k−1)/12.

This improves the old contiguous prefix by **one depth at every t≥5**, without changing its11/12 limiting ratio. The union plus old tip/pretip now leaves `[22+22t,21+24t]`, containing2t depths, before other isolated constructions are added. No full-odd, full-k95 or larger contiguous range follows.

At t1 k47 depth43 and t2 k71 depth65, complete fixed-length results already subsume this consequence. At t3 k95 it gives depth87; at t4 k119, depth109. The lower target20+22t is old q24 coverage. The exact older D8/H1/q30/F18/F20/q22/WholeArm comparison is pinned in the predecessor overlap report: none of those stated families supplies the first missing U_t+1 for t≥5. This is a bounded repository comparison, not worldwide novelty.

## 2. Falsifiable source contract

Before the single gadget search, [contract.md](contract.md) stated the following conditional transfer. The input X is an odd-k word of length2k+1, with H offsets at even indices using0..k, L offsets at odd indices using0..k−1, and consecutive numeric sums0..2k−1, all bijectively. Require

    X[k]=k−1, X[last]=12;
    z odd, 1≤z, z+2<k;
    X[z−1:z+3]=[H1,L0,H0,L2].

These are exactly the needed conditions of the frozen P20/q24 B2 source family. The extra endpoint equation X[0]+12=k follows from the complete inventories and need not be assumed independently. Decoding H_h as2k−h and L_l as l gives a graceful alpha path with cutk−1 and the actual physical midpoint labeledk−1.

Use a B block of length1, tagged L; a D block of length23, tagged H,L,…,H; and an A block of length24, tagged L,H,…,H. Their combined fresh H and L inventories must each be1..24; A must end at H12. The three chains

    H25–B–H0;   L0–D–L26;   H36–A

must have adjacent sums1..50 exactly. The zero edge H0–L0 is separate. The total-sum necessity is satisfied:2·(2·sum(1..24))−12+25+26+36=1275=sum(1..50). Side counts are H12+12 and L1+11+12. These aggregates alone are not the existence proof.

## 3. Literal certificate

The complete directly checked arrays in [data.json](data.json) are

    B = [16]
    D = [1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,9,9,11,21,24,24,23,23]
    A = [14,15,15,10,12,16,10,13,8,11,13,14,17,17,18,18,19,19,20,20,22,22,21,12].

The H inventory is D_even plus A_odd; the L inventory is B plus D_odd plus A_even. Both are1..24 once. Their three chain sum lists are

    [41,16]
    [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,17,18,20,32,45,48,47,46,49]
    [50,29,30,25,22,28,26,23,21,19,24,27,31,34,35,36,37,38,39,40,42,44,43,33].

They partition1..50, with no repetition. This finite certificate establishes the fixed gadget premise. A single bounded CP-SAT9.15.6755 run found it in1.1427864 seconds (four workers, seed21,45-second cap); that status is preserved in `search-result.json` but is **not** a proof premise. No large source-path or new seed enumeration was performed.

## 4. Universal one-step proof

For any X,z satisfying section2, define

    Y=(X[:z]+24) ++ B ++ [H0,L0] ++ D ++ (X[z+2:]+24) ++ A,
    K=k+24.

The two old numeric zeros are removed before the reversed tagged pair is inserted. Since z is odd, the input prefix ends H; B is L; the new zero pair is H,L; D begins and ends H; the retained suffix begins L. The old whole word ends H and A starts L. Thus alternation is correct at every join. The positive old H and L offsets translate to25..K and25..K−1 respectively; the fresh side inventories fill1..24 and the two zeros fill0. Hence Y has the required complete H/L inventories.

Only the old edges of sums1,0,2 are removed. All other old edges translate by48, giving51..2k+47=51..2K−1 exactly. The new three chains give1..50 and the new zero edge gives0. Therefore every required sum0..2K−1 occurs once.

Replacing the two old zeros with B, two zeros and D inserts24 vertices before the old midpoint. The appended A adds24 more vertices after it. The old midpoint consequently moves from k to K and its offset increases24 to K−1. This is the **physical midpoint of the new full path**, not a retained old hub. The terminal is H12. The new H0 is at index z+1 and the new L0 at index z+2. Both remain to the left of the midpoint.

Thus Y is an alpha graceful source for two genuine equal K-arms, simultaneously having maximum2K at depth K−z−1 and zero at depth K−z−2. This argument is symbolic in the entire input word and k,z; no finite t extrapolation is used.

## 5. Unbounded family and actual named-graph transfer

The pinned old P20 source has k0=23,z0=3. Every standard B2 q24 step preserves section2 and changes (k,z) to(k+24,z+2). After exactly t−1 old steps, where t≥1,

    k_in=23+24(t−1), z_in=3+2(t−1)=1+2t.

Apply the new transfer **once, as the final step**. Then K=23+24t and the extreme depths are21+22t and20+22t. The new output is not asserted to satisfy the old `[H1,L0,H0,L2]` window; it does not. Therefore no unjustified self-iteration is hidden in this induction. Starting from the alternate z5 seed would instead give19+22t as upper target, already inside the old band; the z3 P20 seed is essential for the gain.

For completeness, select another actual arm b≠a. Let h=n−2, Q=hK+m and N=nK+m. The residual consisting of the hub, h remaining K-arms and all m original leaves has a root-zero graceful labeling: on residual arm rank i,

    g(i,d)=K(h−i)−(d−1)/2  for odd d;
    g(i,d)=Ki+d/2          for even d;
    g(leaf,j)=hK+j+1, g(c)=0.

Its labels partition0..Q. Hub-arm edge weights are K,2K,…,hK. The other arm weights are |K(h−2i)−u|,1≤u<K. Their block indices are h−2i−1 when h−2i>0 and2i−h otherwise; these permute0..h−1. Original leaf weights fill hK+1..Q. This proves the residual inventories for all h,m, including the singleton h=m=0.

Shift residual labels by K−1. Keep decoded source low labels unchanged and raise every source high label by Q. Identify the source's true midpoint with the residual hub; put indices K−d on arm a and K+d on arm b. The source low, residual and source high bands are `[0,K−1]`, `[K−1,Q+K−1]` and `[Q+K,Q+2K]`, intersecting only at the identified hub. Edge weights are disjoint intervals1..Q and Q+1..N. This is a bijective labeling of the actual named graph. Its low zero gives depth20+22t. Its high extreme becomes N at depth21+22t; complementing **every** vertex label, including residual arms and original leaves, supplies the other requested zero. The two requests use separate labelings.

## 6. Exact controls and limits

[check.py](check.py) imports no solver or predecessor checker. It reads the hash-pinned old literal data, checks both source and gadget inventories, reconstructs old B2 steps and the final transfer, and verifies decoded labels, weights, alpha cut and physical midpoint for100 t-values. This is falsification support for the symbolic proof.

The requested complete sources are retained as [t5-source.json](t5-source.json) and [t6-source.json](t6-source.json):

|t|k|H0 index|L0 index|new maximum-depth zero after complement|
|---:|---:|---:|---:|---:|
|5|143|12|13|131|
|6|167|14|15|153|

Actual-graph tests cover t1,2,3,4,5,6,11,25, n2/3/5, m0/1/2/5, all selected arms and both separate targets: **640 named graphs and473,088 edges**. Normal and optimized Python outputs are byte-identical. Fourteen effective mutants reject wrong B/D/A values or tags, truncation, false extreme indices, false self-iteration, wrong shift, missing whole-graph complement, off-by-one target, omitted original leaves, an old midpoint, wrong depth formula and an incorrect input window. No failed search is converted to a graph obstruction.

This odd B1/reversed-zero step lies outside the previously excluded positive-even-B stationary-window and empty-B contracts. The key change is the tagged zero order and the use of the new step only at the end. Within this specific shape, an odd nonnegative B length is at least1, so H0 cannot occur earlier than index z+1; a second extra depth requires a different interface. This is a statement about this transfer shape only.

## 7. Prior operations, access limits and an additive citation correction

The existing alpha/residual amalgamation is prior art. The old H1 concatenation is exactly the operation in [Hicks–Ollis–Schmitt Lemma4.5's proof](https://community.middlebury.edu/~jschmitt/papers/HicksOllisSchmitt2018.pdf) with alpha rotation, also represented by [Adamaszek2006 Lemma1](https://arxiv.org/pdf/math/0608513); this packet does not rename that operation as new. The precise reversed-zero three-chain operation has not been exhaustively classified against compositions of older insertions. Its historical priority and that of the all-m positional corollary remain UNKNOWN. The earlier q24 priority report's limits remain applicable.

[Luiz–Campos–Richter2017, Lemma4 and Theorem14](https://ic.unicamp.br/~reltech/2017/17-12.pdf) already cover all vertices for the path subfamily n2,m0 and the central-one-leaf subfamily n2,m1. Their Lemma5, attributed to Cattell, is **ordinary graceful** one-vertex/one-label freedom under its listed conditions, not alpha freedom. Lemma4 separately states alpha-zero freedom with the central P5 exception. This corrects the word “alpha-path” in §6 of the frozen predecessor report SHA `fdb2962807a17d09946a01446fcb0afddb7a180c13fbfd674b18f39748daa575`; its original bytes are preserved. The mathematical theorem and Lean gate there are unaffected. The present correction is also recorded separately in [CORRECTION-PRIOR-REPORT.md](CORRECTION-PRIOR-REPORT.md).

Cattell's full original pi-representation construction remains an access gap in this project's bounded comparison. Separate one-point witnesses do not establish a single source with the simultaneous midpoint/cut/extreme positions required here. No absence or novelty claim follows from this access gap. No expert was contacted and no external review is asserted.

## 8. Reproduction and next gate

Run `python check.py` and `python -O check.py`; `verify_freeze.py` checks all frozen payload and predecessor hashes. The complete mathematical proof is sections2–5; the solver is unnecessary for reproduction. Independent post-freeze mathematical QA and then a scoped Lean construction should verify the exact final-step theorem before any release claim.

The next falsifiable depth after this gain is U_t+2=22+22t for t≥5. Any proposed B0/D24/A24 variant must be compared first with the existing empty-B small-sum obstructions; no new search or proof for that interface is included here. Current result is precisely the single-depth prefix extension above, with all n,m and actual named targets.
