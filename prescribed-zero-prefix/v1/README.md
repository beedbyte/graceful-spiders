# Prescribed-zero prefixes in equal-arm spiders

For every integer k≥19, all n≥2,m≥0, any selected long arm of S(k^n,1^m)
and each depth 2≤d≤D8(k), a graceful labeling puts zero at the requested vertex.
Different requests may use different labelings. Both arm-length parities and
the path boundary n=2,m=0 are included.

The sufficient endpoint is 11 for 19≤k≤34, 27 for 35≤k≤52, and
25+16 floor((k−35)/18) for 53≤k≤124. For k≥125 write
p=floor((k−3)/2)=61+11a+r, a≥0,0≤r≤10; then D8(k)=107+20a+2r.
The bound 0≤10k−11D8(k)≤261 gives D8(k)/k→10/11 through all integers.
This is sufficient coverage, without an assertion of optimality or full
zero-rotatability. The predecessor K7 thresholds remain sufficient, without
being identified as the exact inverse of D8.

Read the [technical manuscript](manuscript.md), the shorter
[German](manuscript.de.md) and [Chinese](manuscript.zh.md) presentations,
the [D8 construction](research-audits/graceful-q10-gap-fill-beyond-d7-2026-10-09-a/report.md),
the [separate mathematical check](research-audits/graceful-q10-gap-fill-independent-2026-10-09-a/report.md),
and the [literature addendum](research-audits/graceful-d8-gap-fill-primary-addendum-2026-10-09-a/report.md).
The [verification scope](verification-scope.md) records the exact Lean proof,
copied-source replay and source identities. The formal ratio statement uses an
integer precision criterion. Checks are internal project checks; external peer
review is not recorded and historical priority remains unresolved.

Jordi Gartner publishes this work through Beedbyte; AI tools assisted the
documented core and residue construction, proof development, executable graph
checks, Lean formalization, literature comparison and draft language work.
German and Chinese are shorter substantive presentations rather than full
translations of the English manuscript; human language review is not documented.

## Reproduce

The mathematical checks use Python3.12.1 and its standard library:

```sh
python -B verify_package.py
python -B run_math.py D8-author
python -B -O run_math.py D8-author
python -B run_math.py D8-audit
python -B -O run_math.py D8-audit
python -B run_math.py D7-author
python -B -O run_math.py D7-author
python -B run_math.py D7-audit
python -B -O run_math.py D7-audit
python -B run_math.py D7-author-check
python -B -O run_math.py D7-author-check
```

For a fresh D8 Lean build, provide the recorded Windows Lean4.34.0 executable:

```sh
python -B portable_lean_build.py --lean /path/to/lean.exe --theorem D8
```

The adapter requires compiler SHA-256
`a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`.
A different platform/toolchain needs its own verification. The fresh build uses
only newly compiled local modules and the toolchain's Std, and compares all
706 axiom reports with the frozen inventory. The standard axioms are propext,
Classical.choice and Quot.sound. Lean/Std remain trusted dependencies.

## Distribution identity

This distribution contains exact mathematical source copies and separately
identified manuscript/link and runner overlays. Original environment metadata,
development/compiler objects and superseded draft packages are omitted. Exact
originals and their hashes remain in the internal archive. The mathematical
source programs are byte-identical; run_math.py applies in-memory provenance
lookup adjustments to the D7/D8 author and D8 audit checkers for omitted
environment-bearing report and workspace instructions. Those lookups check
recorded identities and do not claim to reverify omitted files' bytes. The
workspace instructions are not mathematical or Lean premises. No construction
or graph check changes.

PACKAGE-MANIFEST.json authenticates this selected distribution. Original source
manifests describe their original freeze payload, including omitted files;
they are not a claim that those entire historical packages are redistributed.
Source reports retain their freeze-time status text. Current formal status is
recorded separately in verification-scope.md. Earlier published downloads and
repository sources are separate immutable records.
