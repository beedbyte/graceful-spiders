# Independent mathematical QA: terminal-normalized K29 index-4 and index-2 seeds

Frozen 10 October 2026. **GO for the two exact K29 literals, their K119 target pairs, and the all-iteration positional implications under the pinned terminal-normalized append lemma.** This is a private mathematical reconstruction and finite graph check. It is not a new Lean replay, external review, publication, or worldwide-priority finding.

## Exact scope

The two input literals are the `word` arrays in `result.json` from the frozen index-4 and index-2 packets. Their original reports contain malformed hash interpolation and inaccurate low-zero wording; each has an additive correction addendum. I bind both the original report and its corrected addendum below, and rely on the addenda for the result filenames, hashes, and target depths. The original records are unchanged.

* **Index 4 packet:** K29 word has zero indices 3 and 4. At K=119 these give left depths 116 and 115 respectively; the new targets are therefore **115 and 116** on either named arm.
* **Index 2 packet:** K29 word has zero indices 1 and 2. At K=119 these give left depths 118 and 117 respectively; the new targets are **117 and 118** on either named arm.

Each target and arm has its own whole-graph labeling. The supplied residual graph H is arbitrary subject to a conventional graceful labeling `g` into `[0,Q]` and a specified root with `g(root)=0`. H may be disconnected, cyclic, and non-onto. Q=0 is allowed. The result retains the actual old vertices and edges. It does not zero old-H vertices, tips, or several distinct vertices simultaneously.

For every r≥1, K_r=30·4^r−1. The index-4 seed supplies depths K_r−4 and K_r−3; the index-2 seed supplies K_r−2 and K_r−1. Combining these two newly checked packets with the separately checked index-5/6 and index-7/8 packets gives the near-tip family **K_r−8 through K_r−1**, each depth separately selectable on both named arms. This is not a full interior theorem for r>1.

At K=119, the evidence tiers are distinct:

| Depths | Evidence status |
|---|---|
| 1–110 | Frozen copied-source Lean replay of `K119Rooted.interior` |
| 111–112 | Frozen copied-source Lean replay of the terminal-normalized index-7/8 family |
| 113–114 | Separate mathematical QA of the index-5/6 literal and family; no Lean claim from that QA |
| 115–118 | This separate mathematical QA of index-4 and index-2; no Lean claim from this report |

Thus the project-relative **mathematical** coverage is 1–118 at K119 when those separate statements are combined. The checked Lean coverage is only 1–112. The new index-4/index-2 instances have not been replayed/formalized in Lean by this report.

## Independent literal reconstruction

The index-4 word is

```
[1,2,2,0,0,1,4,4,3,3,6,7,9,10,12,13,15,16,18,19,21,22,24,25,26,24,23,21,20,18,17,15,14,12,11,9,8,6,5,5,7,8,10,11,13,14,16,17,19,20,22,23,25,27,29,28,27,26,28]
```

The index-2 word is

```
[1,0,0,2,4,4,3,1,2,3,6,7,9,10,12,13,15,16,18,19,21,22,24,25,27,27,26,24,23,21,20,18,17,15,14,12,11,9,8,6,5,5,7,8,10,11,13,14,16,17,19,20,22,23,25,26,29,28,28]
```

The separate checker parses only these literal JSON files, never the seed search program, serialized solver model, or packet checker. For each word X it verifies length 59, even-index inventory `[0,29]`, odd-index inventory `[0,28]`, adjacent-sum inventory `[0,57]`, terminal X[58]=28, X[0]=1, and the exact zero-index pair. The endpoint condition can also be recovered algebraically: the side inventories give sum(X)=29²; adjacent sums total 2·29²−X[0]−X[58]=1653, while 0+…+57=1653, hence X[0]+X[58]=29. With terminal 28, the first tag is 1.

## Append and all-r preservation

I independently reconstructed and implemented the explicit residue-three append. For odd k≥3 put s=k+1=2h and p=3s=6h. Form a by concatenating the pairs

* `(3j+1, 6h−3−3j)` for j=0,…,2h−1;
* `(6h−1−3j, 3j+2)` for j=0,…,h−1.

These entries partition `[0,p−1]`. The internal pair and between-pair differences of the first block give the 2-mod-6 and 4-mod-6 classes; its between-pair differences give the 5-mod-6 and 1-mod-6 classes, with the block join supplying 6h−1. The second block's within-pair and between-pair differences give the positive 3-mod-6 and positive 0-mod-6 classes. Together these are exactly `[1,p−1]`.

Set y_i=a_i for even i and p−1−a_i for odd i. Let C be y followed by the reverse of p−1−y. Since p is even, reversal changes parity: each parity class of C consists of one parity class of a and the complementary values from the other parity class, so both C parity inventories are `[0,p−1]`. For each a-edge difference δ, the two halves supply the paired sums p−1−δ and p−1+δ; the middle join supplies p−1. Thus C has all adjacent sums `[0,2p−2]`. Directly from the formula, C[0]=1, C[2s]=p−1, and C[2p−1]=p−2.

Append Z_i=C_i+k+(i mod 2) to X. Since X has odd length 2k+1, local even indices become global odd indices (the low side), and local odd indices become global even indices (the high side). The appended low tags are k,…,k+p−1 and high tags k+1,…,k+p. The old inventories therefore extend to low `[0,K−1]` and high `[0,K]` for K=k+p=4k+3. The join sum is 2k; internal new sums are 2k+1,…,2K−1, filling the full sum inventory after the old 0,…,2k−1. The new terminal is (p−2)+k+1=K−1.

The new midpoint index K is local tail index K−(2k+1)=2k+2=2s, so its offset is (p−1)+k=K−1. Every old index is unchanged. Iteration from k=29 gives K_r+1=4(K_{r−1}+1), hence K_r=30·4^r−1; the four literal zero indices from these two words remain fixed at 1,2,3,4 for every r. The terminal-normalized append report supplies the same general operation; the exact source/result hashes are pinned below. This report's small r=1,2,3 executable runs are transcription checks, not the proof of the unbounded recurrence.

Decode each even tag x_i as 2K−x_i and each odd tag as x_i. The side inventories give the full label permutation `[0,2K]`. Each adjacent edge difference is 2K minus its tag sum, so all weights `[1,2K]` occur once. The midpoint index K is odd and has label K−1. Every edge crosses cut K−1: odd-position labels are ≤K−1 and even-position labels are ≥K.

For an original zero at index i, the left depth is K−i. Reversing the source path places it at right index 2K−i, the same outward depth. At odd zero indices 1 and 3 the path label is 0; at even indices 2 and 4 the label is 2K. This yields the four depth formulas stated above.

## Actual graph transfer

Let c=K−1 and N=Q+2K. Identify the source path midpoint with the supplied root of H. Label each old vertex v by c+g(v). Keep noncentral path labels ≤c and add Q to every path label above c. The new low path vertices occupy `[0,c−1]`; old H vertices occupy an injective subset of `[c,c+Q]`; new high path vertices occupy `[K+Q,2K+Q]`. These bands are disjoint, including when H omits permitted labels. Every H edge keeps its weight in 1,…,Q. Each of the 2K path edges crosses c, so its weight increases by Q, giving Q+1,…,Q+2K. The full edge weights are therefore 1,…,N. No connectedness, acyclicity, vertex-onto, or source-root output condition is used.

A low-zero target remains 0 under this graft. A high-zero source target has label 2K+Q=N; complement **the entire graph** by f↦N−f to set that target to zero while preserving injectivity and all edge weights. Reversing the source path chooses the other named arm and fixes its midpoint. This proves separate actual-graph zero labelings, not merely abstract path certificates.

The independent checker instantiated K=119, 479, and 1919 for each seed (the infinite statement follows from the preceding algebra). At K=119 it checked both depths on both arms for four root-zero supplied residuals: singleton (Q=0), one edge (Q=1), non-onto triangle (Q=3), and cyclic disconnected K4 plus an isolated vertex (Q=6; labels 0,1,4,6 on K4 and 2 on the isolate). These are 16 actual named-graph cases per seed and 3,848 actual edges checked per seed. At K=479 and K=1919, it repeats all four graph examples at each selected depth and arm. Those larger checks are finite corroboration only.

Five effective semantic controls reject: a changed terminal, a false midpoint index, an off-by-one target, omission of right-arm reversal, and omission of the whole-graft complement. All invariants use explicit exceptions, not Python `assert`. Normal Python and `python -O` outputs are byte-identical.

## Evidence pins and limits

| Input/evidence | SHA-256 |
|---|---|
| Index-4 original report | `81e75722dfdf469502076fe7e20201679e43c1fcbf3f7ed5f367897cb764aac7` |
| Index-4 corrected addendum | `d502660b55dedd36f71425b65b072f62804bdfa63f860eaf3d174ac57006b0f2` |
| Index-4 literal `result.json` | `af466f84614f492debfd28a396af2cddcaf2a2547d6efaa4605dbd341e544cf6` |
| Index-2 original report | `1d5d73086b11d0e885be86b2076e4a91c7588970ea7e36d168c1b3da40dd9d38` |
| Index-2 corrected addendum | `ba39f587ca51a0fbec4622757d808a53027f4a17fb8fbaef857c435a1849b5b3` |
| Index-2 literal `result.json` | `0d8b0c0164b98fcd3e28ee7d95016cd43aa4d7355c9ad94ff0fe317ab4bf9e93` |
| General append independent math report | `8199fae12d7157155399a325cad444dcc3c7d1a0fa578975f1f917e892b81462` |
| Terminal-normalized independent Lean replay (index 7/8, K−8/K−7) | `6ea372525ae4eea67d58dbf113e36f24ec29bdc6c411210fb828d6ecb555de9a` |
| K119 interior copied-source replay (depths 1–110) | `d2052524d5d4a94c96df2974b6e37b79888a556dd229ba368c13d7b920d31705` |
| K119 index-5/6 mathematical QA (depths 113/114) | `d4d199253e998157c6ef052a7bd0316ac03e0ba066de1c41ee97bdb361575e96` |
| Independent checker | `3760F097B4D57C172B4DBFE537324B8B011DC7F40C4FA5743C96DA61F16D2997` |
| Normal and optimized checker outputs (identical) | `B9A526A40F1E361AF9E61997165F9CF952919D90F877C71AB2A84860515C48B5` |

This independent QA did not execute either seed search/model/checker, and made no seed search. The generic alpha-cut graph graft and endpoint-matched append are established operations; no worldwide priority claim is made. The K119 formal coverage remains 1–112, while 113–118 here are mathematical evidence only. Historical literature coverage and priority remain **UNKNOWN**. No public repository, CMS, website, or profile was written.

Reproduce from the project root:

```
python research-audits/graceful-k119-terminal-k29-seeds-independent-2026-10-10-a/check.py research-audits/graceful-k119-terminal-k29-seeds-independent-2026-10-10-a/normal.json
python -O research-audits/graceful-k119-terminal-k29-seeds-independent-2026-10-10-a/check.py research-audits/graceful-k119-terminal-k29-seeds-independent-2026-10-10-a/optimized.json
```

Compare the two output files byte-for-byte. The checker binds literal and correction-addendum hashes before processing.
