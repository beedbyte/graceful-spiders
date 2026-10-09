# Internal growing-depth alpha paths

Read proof.md for the exact quantifiers and all-parameter proof.

For s>=1, r>=3s, r!=3s+1 and k=2r+1, the formula gives a
midpoint alpha path with zero/maximum at depths 4s,4s+1.
Known alpha-amalgamation gives the two separate prescribed-zero
spider labelings for all n>=2,m>=0. The guaranteed depth count
grows with k; this is still partial coverage.

Reproduce with Python 3, without optimization flags:

    python construct.py
    python verify.py

The verifier is standard-library only. It imports no constructor
or solver. The recorded run passed 156 paths and 960 full spiders.
Two deliberately corrupted certificates were rejected. No finite
run substitutes for the proof; no separate-agent audit has been
completed yet.

probe.py and probe-results.json retain the initial bounded
whole-arm CP-SAT discovery, with depth 8 fixed. Running that
optional script requires the pre-existing neighboring vendored
OR-Tools package. It is unnecessary to construct or verify the
proved family. Its r=7 INFEASIBLE result concerns only the
specified auxiliary side sets and endpoints; no global
nonexistence follows.

SHA256SUMS.txt pins the files delivered for independent review.
Re-running generation/checking should preserve data content,
but any later edit requires a new frozen manifest and audit.

Existing Walecki/path/doubling, Patterson/Rofa center-zero,
and Huang-Kotzig-Rosa composition ingredients are acknowledged.
Cattell's full construction comparison remains unresolved.
No worldwide novelty, full all-odd zero-rotatability, publication
approval, or external peer review is claimed.
