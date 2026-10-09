# Growing prescribed-zero depths in equal-arm spiders

Version `gd-2026-10-09-v1.1`, dated 9 October 2026. The exact theorem passed an internal proof reconstruction by a separate AI agent. A focused primary-source comparison was completed with the access limitations recorded below; historical priority remains unresolved.

## Theorem

For all integers `s>=1`, `r>=3s`, `r!=3s+1`, put `k=2r+1`. There is an explicit alpha-labeling of `P_(2k+1)` with midpoint label and threshold `k-1`, zero at depth `4s` and maximum `2k` at adjacent depth `4s+1` on the same arm. Endpoint labels are `(3k-1)/2` and `(3k+1)/2`.

Consequently, for every integer `n>=2`, `m>=0` and each specified long-arm vertex of `S(k^n,1^m)` at depth `4s` or `4s+1`, there exists a graceful labeling giving that vertex zero. These are separate labelings, chosen according to the vertex. Depth means edge distance from the designated center, including the path case.

For every odd `k>=11`, all depths `{4s,4s+1:1<=s<=floor((k-5)/6)}` are covered: at least `2 floor((k-5)/6)` distinct depths. The exact set is `I_r={s>=1:3s<=r and r!=3s+1}`; when `k=6t+1`, `s=t` gives an additional pair beyond that lower bound. The exclusion is a formula limitation, not an impossibility theorem.

This does not prove full zero-rotatability, all-depth coverage for every odd length, or an alpha-labeling at every zero position. The earlier complete prescribed-zero result for `k in {3,5,7,9,11}` remains a separate result.

## Files and reproducibility

`source/proof.md` contains the all-parameter argument and historical limitations. `source/construct.py` generates formula certificates; `source/verify.py` checks them without importing the generator or a solver. `source/certificates.json` stores 156 paths and 960 complete spider labelings. `source/verification-results.json` records the author's run, with two corruptions rejected. Those finite checks do not prove the unbounded statement. `source/probe.py` and `source/probe-results.json` retain optional bounded discovery evidence, not a proof premise.

On a disposable copy, with standard Python 3 and no optimization flags, run:

```text
cd source
python verify.py
```

This rewrites `verification-results.json`. To regenerate the certificates first, run `python construct.py`, then `python verify.py`; these commands can alter files and must not run against the frozen original. The optional probe requires the neighboring vendored OR-Tools installation described in the source README and is not a standalone package dependency. It is unnecessary for the theorem or checker. A bounded INFEASIBLE result concerns only the tested ansatz.

`manifest.json` lists file roles, sizes and SHA-256 values; `SHA256SUMS.txt` pins this versioned package. `source/SHA256SUMS.txt` preserves the original frozen manifest. A checksum match confirms identity, not validity or novelty.

## Prior work and provenance

Walecki order, older path/alpha constructions, residual center-zero labeling, and Huang–Kotzig–Rosa alpha-amalgamation are existing ingredients. The source proof identifies Patterson and Rofa and records that attribution to the 1982 composition paper currently comes through later sources. Earlier prescribed-zero theorems cover `n=2,m=0` and `n=2,m=1`; those cases are not new coverage. A complete comparison with Cattell's full paper and related constructions remains outstanding. Priority and non-subsumption are unresolved. No first-proof, solved-conjecture, or worldwide-originality claim is made.

An AI agent derived the formula and proof. A separate AI agent independently reconstructed the proof and certificates, and another AI agent checked sources. AI assistance also prepared the release wording and translations. The public research signature is School Scotty. Jordi Gartner is responsible for editorial publication. No human mathematical proof review occurred. The internal audit is not external human peer review or proof-assistant verification; these statements concern this result rather than authorship of the entire website.

Earlier public versions and their proof files retain their own scope and history. Corrections to this package require a new reviewed version. The existing repository has no selected license.

## Completed internal review

`reviews/independent/audit-report.md` records mathematical GO for the exact theorem, without a gap or counterexample, and conditional policy GO as a larger project advance. It gives NO-GO for claiming a major novel literature result on the available evidence. `reviews/prior-art-report.md` records the checked ingredients and boundary cases; Cattell's full construction, older original path texts, and a complete citation-chain comparison remain gaps. No historical non-subsumption conclusion follows from failing to identify a directly subsuming statement.

The independent agent reconstructed all 156 saved paths and 960 saved full spiders exactly, checked 7,710 further admissible path pairs and 7,040 further spider labelings, and rejected 13 negative controls. Additional large cases also passed. These are finite implementation checks; the all-parameter conclusion follows from the independent proof reconstruction. `reviews/rc1-language-scope-audit.md` is the historical review whose terminology and version-note recommendations were applied in this release wording.

From this directory of a disposable copy, run the independent checker with the copied source explicitly supplied:

```text
python reviews/independent/independent_check.py source
```

It writes `results.json` and `certificate-hash-comparison.json` beside itself. The source and original review records are preserved as dated snapshots. The original source and review copies remain byte for byte; references and historical pending-review language inside them retain their original dated context. The current disposition is the one stated in this README and the completed audit reports.

## Research note

[English](notes/article.en.md), [Deutsch](notes/article.de.md), [中文](notes/article.zh.md). The German and Chinese translations await human language review. The notes share the exact theorem and source boundaries; they do not establish full zero-rotatability or historical priority.
