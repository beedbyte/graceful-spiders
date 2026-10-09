# Growing prescribed-zero depths in equal-arm spiders

Version gd-2026-10-09-v1.1 · 9 October 2026.

## Abstract

We give an explicit construction for an increasing set of prescribed zero positions in equal-arm spiders. Let `s>=1` and `r>=3s` be integers with `r!=3s+1`, and set `k=2r+1`. The construction produces an alpha-labeling of the path `P_(2k+1)` with midpoint label `k-1` and alpha threshold `k-1`, zero at depth `4s`, and maximum `2k` at the adjacent depth `4s+1` on the same arm. Its endpoint labels are `(3k-1)/2` and `(3k+1)/2`. Established alpha-amalgamation and complementation then give, for every integer `n>=2` and `m>=0`, a graceful labeling of `S(k^n,1^m)` with zero at any prescribed long-arm vertex of depth `4s` or `4s+1`. These are separate labelings. For every odd `k>=11`, at least `2 floor((k-5)/6)` distinct depths are covered. This is partial prescribed-zero coverage; mathematical priority remains unresolved.

## Scope

Here `S(k^n,1^m)` has `n` arms of length `k` and `m` arms of length one, with length measured in edges. Depth is distance from the designated center, including the path case `n=2,m=0`. For every permitted tuple and each specified vertex at one of the two depths, there exists a labeling assigning that vertex zero. The labeling may depend on the vertex; two vertices are not assigned zero in one labeling.

For a fixed `r`, the exact index set is `I_r={s>=1:3s<=r and r!=3s+1}`. The uniform bound uses all depths `{4s,4s+1:1<=s<=floor((k-5)/6)}`. When `k=6t+1`, the exact construction also admits `s=t`. The exclusion `r=3s+1` restricts this formula and is not a nonexistence result. No coverage is asserted here for all depths, full zero-rotatability, all spiders, or an alpha-labeling at every zero position. Previous center and other boundary-depth constructions are separate established ingredients.

## Version note

Adds a construction for prescribed zeros at long-arm depths 4s and 4s + 1 in S(k^n,1^m), where k = 2r + 1, s ≥ 1, r ≥ 3s, r ≠ 3s + 1, n ≥ 2, and m ≥ 0. The number of guaranteed depths grows with k; this is not a full zero-rotatability result. The two zero positions use separate spider labelings.

## Evidence and review status

The all-parameter proof has passed an internal audit by a separate AI agent, which independently reconstructed the permutation, both extensions, the full path, and the complete spider composition. It exactly reconstructed the 156 saved paths and 960 saved spider labelings, checked 7,710 further admissible path pairs and 7,040 further spider labelings, and rejected 13 negative controls. These finite checks support implementation and integrity; the unbounded conclusion follows from the reconstructed proof. This was an internal AI-agent audit, not human peer review or proof-assistant verification. The separate focused source review found no checked statement supplying all the simultaneous constraints; Cattell's full construction and older original texts remain access gaps, so priority and historical non-subsumption remain unresolved.
## Contribution and provenance

The result presented here is the explicit construction and its increasing prescribed-depth guarantee, proved in the supplied argument and internally audited. Classical Walecki order, older path/alpha constructions, center-zero labelings, and Huang–Kotzig–Rosa alpha-amalgamation are existing ingredients. Patterson and Rofa document relevant constructions; the Huang–Kotzig–Rosa attribution is currently supported through later sources. Earlier work already covers all prescribed zeros in `n=2,m=0` and `n=2,m=1`; those cases cannot support a claim of new coverage. Cattell's full construction and related older machinery have not yet been compared completely, and may subsume parts of this argument. No first-proof or worldwide-originality claim is made.

An AI agent derived the formula and proof. A separate AI agent independently reconstructed the mathematics and checked the certificates, and another AI agent reviewed the source literature. AI assistance also prepared the English release wording and German and Chinese translations. The public research signature is School Scotty. Jordi Gartner is responsible for editorial publication. No human mathematical proof review has occurred. These statements describe this result's observed workflow; they do not attribute the entire website to AI or claim external peer review or proof-assistant verification.
