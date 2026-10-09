# Independent audit of the whole arm construction

Date: 9 October 2026. Frozen input: `../graceful-whole-arm-next-2026-10-09`. This is a separate agent's mathematical and computational audit. The input package was not edited. No website, GitHub, or other public destination was modified.

**Mathematical verdict: GO for the exact theorem in Sections 1–5 of the frozen proof.** No gap or counterexample was found. The conclusion follows for unbounded parameters from the permutation, sum, vertex, and edge partitions reconstructed below; it does not rely on extrapolating the finite runs.

**Project-policy publication assessment: conditional GO as a larger project advance, with the precise partial-coverage and source caveats below.** The growing prescribed-depth set is a substantive advance over a fixed set of depths. The owner's actual policy does not require certified worldwide priority. Its mathematical countercheck prerequisite is now satisfied for this frozen input. Release packaging must still identify the same version, files, and hashes across destinations, include this independent audit, and retain the checked source boundaries. This audit makes no public writes.

**Stronger assessment as a major novel result in the literature: NO-GO for that characterization on the present evidence.** Mathematical priority and non-subsumption by older alpha-path constructions remain unresolved. No direct older theorem subsuming the simultaneous constraints was identified. This stronger NO-GO rests on unresolved provenance and the lack of an established novelty contribution, not on a demonstrated mathematical redundancy, and must not be used as an extra worldwide-priority requirement in the owner's publication policy.

## Exact mathematical scope

For integers `s >= 1`, `r >= 3s`, `r != 3s+1`, put `k = 2r+1`. The formula produces an alpha-labeling of the path with `2k+1` vertices and `2k` edges, with the following properties simultaneously:

- The designated midpoint has label `k-1` and the alpha threshold is `k-1`.
- On the chosen arm, the vertex at depth `4s` has label zero and the vertex at depth `4s+1` has label `2k`.
- The ordered endpoint labels in the source orientation are `3r+1` and `3r+2`, equivalently `(3k-1)/2` and `(3k+1)/2`.

For every `n >= 2`, `m >= 0`, and every specified long arm of `S(k^n,1^m)`, the composition produces one graceful labeling with zero at depth `4s`; its complement produces another with zero at depth `4s+1`. The labeling depends on the specified vertex. These are two separate prescribed-zero conclusions.

The domain includes `s=1,r=3,k=7`. Its smallest excluded gap is `s=1,r=4,k=9`. The exclusion is a limitation of the construction, not a graph nonexistence assertion. Depths are valid because `4s+1 <= 6s+1 <= 2r+1`.

## Independent proof reconstruction

Write `p=3s`. The first `2s` entries of the auxiliary permutation are the residue-1 values in increasing order interleaved with the residue-0 values in decreasing order. The remaining residue-2 values occur in alternating largest/smallest order. The residue classes are disjoint and exhaust `[0,p-1]`, proving the vertex permutation assertion without assuming gracefulness.

The first portion has `2s-1` differences `|p-4-3i|`, `0 <= i <= 2s-2`. The signed terms are all 2 modulo 3 and cannot be zero. Their positive terms give the residue-2 integers through `p-4`; their negative terms, after taking absolute values, give the residue-1 integers through `p-2`. Thus they give exactly the nonmultiples of 3 in `[1,p-2]`. The next edge contributes `p-1`. The tail contributes the multiples `3(s-1),...,3`. These sets are disjoint and exhaust `[1,p-1]`. At `s=1`, the first positive progression and the internal tail edges are empty, while the permutation is `1,0,2`; the proof still works.

For the doubled core, assign `y_i=a_i` at even indices and `y_i=p-1-a_i` at odd indices, then reflect with complementation. A reflected index is `2p-1-i`, which has the opposite parity to `i`. Consequently each original entry contributes its `a_i` value to the high side and its complement to the low side. Both side multisets are exactly `[0,p-1]`. Each edge of the first half has sum `p-1` plus a signed difference from `a`; its reflected partner has sum `p-1` minus that signed difference. Because the absolute differences are exactly `[1,p-1]`, these pairs supply `[0,2p-2]` except `p-1`; the central edge supplies the missing value. No collision remains possible.

The core begins with high offset 1 and ends with low offset `p-2`. The original indices `2s-1` and `2s` are respectively `0` and `p-1` in `a`. Their reflected indices are `4s` and `4s-1`, so their one-based positions are `4s+1` on the high side and `4s` on the low side. Both offsets are zero. This checks the reflection and depth conventions explicitly.

At size `b`, the four-entry append supplies high offsets `b+1,b` and low offsets `b+1,b`. Its incoming and internal sums are `2b-1,2b+2,2b+1,2b`; hence it adds precisely the next four values and ends with low offset `b`, which is the required endpoint for size `b+2`. If `r-p` is even, repeat to size `r` and append high offset `r+1`. The last incoming sum is `2r-1`.

If `r-p` is odd and admissible, it is at least 3. Repeat to size `b=r-3`. The terminal seven entries have incoming/internal sums `2b-1,2b+1,2b,2b+2,2b+4,2b+3,2b+5`, the consecutive interval `[2b-1,2b+5]`. Their new low offsets are `b,b+1,b+2`, while their new high offsets are `b,b+1,b+2,b+4`. Therefore both branches give a sequence of `2r+1` entries with high set `[0,r-1] union {r+1}`, low set `[0,r-1]`, initial high 1, final high `r+1`, and sums exactly `[0,2r-1]`. Neither branch changes the two specified zero offsets.

Converting high offset `H` to `4r+2-H` and retaining low offsets gives left labels `[0,r-1]` and `{3r+1} union [3r+3,4r+2]`. The independently reconstructed right arm has lows `[r,2r-1]` and highs `[2r+1,3r] union {3r+2}`. The midpoint is `2r`. These sets partition every vertex label `[0,4r+2]`, with alternating sides across threshold `2r`.

The right arm, including the center edge, supplies differences `[1,2r] union {2r+2}`. The left center edge has difference `2r+1`. Every remaining left difference is `4r+2-(H+L)`, so these edges supply `[2r+3,4r+2]`. The edge sets are disjoint and exhaust `[1,4r+2]`. This proves gracefulness and the alpha condition for the entire path. The final high offsets give exactly the stated endpoints; the retained zeros give the asserted zero and maximum positions.

## Boundary cases and the depth count

At `r=3s`, the bare doubled core plus its final high suffices: no empty-loop or parity assumption is missing. At `r=3s+2`, exactly one four-entry append is needed. At `r=3s+3`, the odd terminal patch follows the bare core. These are the first cases of every route. The checker exercises each at every `s` in its exhaustive rectangle and at large `s`.

The exact index set is `I_r={s >= 1:3s <= r, r != 3s+1}`. Its size is `t` for `r=3t`, `t-1` for `r=3t+1` with `t>=1`, and `t` for `r=3t+2`; at `r=1` the set is simply empty. No uniform formula using `t-1` at `t=0` should be interpreted as a negative cardinality.

For odd `k>=11`, put `r=(k-1)/2`. If `1 <= s <= floor((r-2)/3)`, then `3s <= r-2`; hence the excluded equality `r=3s+1` is impossible. Distinct indices give disjoint pairs `{4s,4s+1}`, so there are exactly `2 floor((r-2)/3) = 2 floor((k-5)/6)` depths in the displayed guaranteed subset. This is a lower bound on total coverage, not the exact size of the construction's set for every `k`. At `r=3t`, the exact construction adds the pair for `s=t`; the first such example is `k=7`, where the lower-bound expression is zero but the construction supplies depths 4 and 5. At `k=11`, the lower-bound subset is `{4,5}` as claimed.

The smallest arm length in the theorem is 7; `k=9` has no index supplied by this formula. Missing depths such as 2 and 3 modulo 4 remain outside the displayed construction, although other results may cover individual cases. No full zero-rotatability conclusion follows from a growing partial set. No counterexample inside the stated domain was found, and the symbolic partitions leave no untreated admissible parameter branch.

## Complete spider argument

Put `h=n-2`, `Q=hk+m`, and `A=k-1`. The residual tree has center zero. Its even-depth labels on residual arm `i` fill `[ik+1,ik+r]`. Reindexing its odd-depth interval by `j=h-i-1` gives `[jk+r+1,(j+1)k]`. Together with the even interval for index `j`, this is exactly the full block `[jk+1,(j+1)k]`. Thus the residual arm labels fill `[1,hk]` without overlap. The short leaves add `[hk+1,Q]`.

The residual center edges are `(h-i)k`, all positive multiples of `k` through `hk`. The internal differences of arm `i` are `|(h-2i)k-u|`, `1 <= u <= k-1`. When `h-2i >= 1`, they form block index `h-2i-1`; otherwise they form block index `2i-h`. For `h=2l`, the positive branch gives odd indices `2l-1,...,1`, while the other branch gives even indices `0,...,2l-2`. For `h=2l+1`, these are respectively even indices `2l,...,0` and odd indices `1,...,2l-1`. Therefore the internal edge sets partition all the open `k`-blocks, and the residual differences are exactly `[1,Q]` after including leaves. This handles all parities and arbitrary arm counts. At `h=0`, the arm lists are empty; at `h=m=0`, there is one center vertex and no residual edge.

Identify this center with the path midpoint. Shift every residual label by `A`, retain every path label at most `A`, and shift every high path label by `Q`. The intervals `[0,A]`, `[A,A+Q]`, and `[A+Q+1,2k+Q]` have only the intended overlap at the identified center. Their labels exhaust `[0,nk+m]`. The residual differences remain `[1,Q]`; every path difference increases by `Q` because every path edge crosses the threshold. Thus path differences become `[Q+1,Q+2k]`, proving gracefulness for the full spider.

The zero at depth `4s` is retained and the adjacent maximum becomes `nk+m`. Complementing all labels about `nk+m` gives the separate depth-`4s+1` zero labeling. Choosing the selected long arm and any distinct companion arm is valid for `n>=2`; arm permutations reach any requested arm. The finite checker enumerates every graph vertex and edge from the spider parameters independently of the labeling formula, including `n=2,m=0`, `n=2,m>0`, both residual-arm parities, and nonzero selected-arm indices.

## Computational evidence and integrity

`independent_check.py` was written from the mathematical formulas and certificate schema. It does not import, execute, or inspect the contents of the submitted `construct.py`, `verify.py`, or solver. Those files were read as raw bytes solely for SHA-256 verification. The author checker is not used as an oracle. The independent implementation additionally validates each intermediate residue, sum, vertex, and edge partition. Explicit checks raise exceptions, so correctness checks do not disappear with Python optimization flags.

All eight entries of the frozen `SHA256SUMS.txt` matched, both before and after the run. The manifest itself has SHA-256:

`3bdbaf6a25095381c61deef0d4ec48cafe86eb0e2848dbe1d8632e8527a1796a`

The saved `certificates.json` file has SHA-256:

`2f1ca7584b6ee5ccff37ce79f5f0fcea1aec5fc65e73c425700a77f65f68a05c`

The canonical JSON hash of all saved certificates and the hash of the entirely reconstructed certificate object both equal:

`da4d1180822e5d353f22fb231b96cab87951e2271bd4fe6f5beab5a1f546820f`

Canonicalization is UTF-8 `json.dumps(value, sort_keys=True, separators=(',', ':'))`. Its hash is deliberately distinguished from the source file's whitespace-dependent hash. `certificate-hash-comparison.json` records matching saved/reconstructed hashes for every individual record. Every path list and every spider label dictionary also compared equal directly.

| Check | Result |
|---|---|
| Frozen saved paths | All 156 valid and exactly reconstructed |
| Frozen saved full spiders | All 960 valid and exactly reconstructed |
| Additional admissible path rectangle | All 7,710 pairs with `1<=s<=60`, `3s<=r<=220`, `r!=3s+1` pass |
| Large path cases | 21 pairs with `s` in `{100,1000,10000}`, gap in `{0,2,3,4,5,20,21}` pass; largest `r=30021,k=60043` |
| Additional spider grid | All 7,040 labelings: `s=1..4`, gap in `{0,2,3,4,5}`, `n=2..9`, `m` in `{0,1,2,7}`, every selected arm, both depths |
| Large or unbalanced parameter spiders | Four further cases, including 101 long arms and 1,000 short leaves, pass |
| Exact index and lower-bound arithmetic | All `1<=r<=3000` checked |
| Negative controls | All 13 rejected |

The negative controls cover a duplicate label, a permutation-preserving path corruption, a graceful reversed path with the prescribed side wrong, a graceful complemented path with the midpoint wrong, a permutation-preserving spider corruption, a missing spider vertex, a correct spider with the wrong requested zero depth, five out-of-domain parameter choices, and a naive excluded-gap continuation. In particular, checks of gracefulness alone cannot pass the reversed/complemented witnesses without checking the stated anchors as well.

To reproduce from this directory, run `python independent_check.py`. An optional argument gives the frozen source directory. The checker writes only `results.json` and `certificate-hash-comparison.json` beside itself. These finite checks support transcription and integrity; the unbounded theorem is justified by the proof reconstruction above. They do not exhaust all graceful labelings or prove nonexistence for excluded parameters.

## Prior ingredients and publication assessment

The object proved here is a path with simultaneous midpoint/threshold, zero-depth, adjacent-maximum-depth, and endpoint constraints, followed by an established composition. It is stronger than merely asserting that a path or equal-arm spider is graceful. It also has different quantifiers from a theorem that assigns one chosen label to one chosen path vertex. Separate one-vertex existence statements cannot be combined into one labeling without an additional argument.

Cattell's 2007 publisher abstract explicitly treats chosen vertices and chosen labels, alpha conditions, and pi-representations, with results of Kotzig and Rosa. Its scope is not confined to endpoints. The direct full-text request failed with HTTP 403; the publisher abstract was available through indexed retrieval. This audit therefore cannot determine whether its machinery subsumes the doubled core, the residue-3 permutation, or the simultaneous constraints. The stronger constraints here do not by themselves prove originality. [Cattell publisher record](https://www.sciencedirect.com/science/article/pii/S0012365X07001215), DOI `10.1016/j.disc.2007.03.046`.

The residue-2 tail is the familiar Walecki alternating order. Its elementary difference sequence and the core doubling are fully proved here, which settles their correctness without settling their historical provenance. No new-operation claim is justified for the alternating order or for the general conversion between graceful permutations and alpha paths. A direct comparison of exact permutation and doubling identities with older constructions remains necessary for a novelty claim.

The local full-text extraction of Patterson's 2017 thesis was inspected at Corollary 2.4.3 and Theorem 3.2.1. The former records the symmetric-spider center-zero result. The proof of the latter uses the same shifts as this composition, after an alpha-side complement if needed. It attributes the joining result to Huang, Kotzig, and Rosa. The frozen proof's attribution is reasonable; the original 1982 paper was not independently retrieved in this audit. The current live request for the thesis PDF timed out, so this check used the existing local extraction. [Patterson institutional full text](https://cardinalscholar.bsu.edu/server/api/core/bitstreams/b44ff232-a480-4d64-aa44-8dff4535e28c/content).

The original institutional report by Luiz, Campos, and Richter was retrieved. Its Lemma 4 records the path prescribed-zero result, and Theorem 14 gives zero-rotatability after attaching one leaf at a central path vertex. Consequently `n=2,m=0` and `n=2,m=1` are already covered as prescribed-zero existence statements. Those cases cannot establish additional coverage in the literature. [Original report IC-17-12](https://ic.unicamp.br/~reltech/2017/17-12.pdf).

Relative to the preceding fixed-depth project construction, allowing a number of depths that grows linearly with `k` is a clear increase in proven scope. This audit does not independently certify the historical claim about every older restricted trade class; that claim is not a premise of the mathematical proof. Nor does increased scope within the project establish worldwide priority. No specific prior construction was shown to imply the full statement; Cattell's pi-representations and earlier permutation/doubling constructions are concrete comparison targets whose contents may establish overlap, not evidence that such overlap has already been found.

The governing local rule is [publication-policy.md](../../publication-portals/publication-policy.md), dated 8 October 2026. It says a larger advance may be published when “Aussage und Geltungsbereich präzise sind, Beweis oder Daten mit Prüfanleitung vorliegen, eine getrennte Gegenprüfung keine Lücke findet und die Quellenlage geprüft ist.” It also requires the website and repository to use the same version, files, and hashes, and treats wider-platform selection for a publication-ready major result as a further decision. It expressly describes itself as a publication filter rather than proof of novelty or correctness. There is no requirement here to certify worldwide priority.

Under that actual policy, this independently checked increase from a fixed depth set to an unbounded count for every odd `k>=11` can reasonably qualify as a larger project advance. The precise theorem, full proof, reproduction instructions, independent countercheck, and focused source boundary are present. A release framed as project progress therefore receives conditional editorial GO, subject to matching the frozen release artifacts and honestly describing the limited source comparison. A claim of a major novel contribution to the literature does not receive GO: the unresolved exact-core/doubling provenance and Cattell machinery prevent that stronger conclusion. Priority uncertainty alone is not a reason to deny the restrained project-progress release authorized by the owner's standard.

Any future public claim must retain the formula exclusion, separate-zero quantifier, partial-depth scope, existing composition attribution, prior degenerate coverage, and unresolved priority status. The separate policy decision about the newer external publication platforms remains with the owner; this report does not select or publish to them.

No claim of full zero-rotatability, a solution of a general graceful-tree conjecture, human peer review, or proof-assistant verification follows from this GO. No mandatory mathematical correction to the frozen theorem was identified.
