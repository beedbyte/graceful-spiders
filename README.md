# Graceful spider trees with three equal long arms

This repository accompanies the [research note on Beedbyte](https://beedbyte.tech/publications/three-arm-spider-zero-rotatability). It contains exact certificates and small Python programs for two stated families of spider trees.

For each `k ∈ {3, 4}` and integer `m ≥ 1`, let `S(k,k,k,1^m)` have three arms of length `k` and `m` leaves joined directly to its center. The note proves that every vertex can receive label `0` in some graceful labeling of this tree. The proof uses one base certificate for each vertex orbit and a fixed-threshold rule for adding center leaves. The computer checks verify the base data and 100 consecutive instances of that rule; the written induction gives the result for all `m`.

## Read the note

- [English](notes/paper.en.md)
- [Deutsch](notes/paper.de.md)
- [中文](notes/paper.zh.md)

These files are GitHub-readable copies of the public Version 1 note. Their project-page links were changed from site-relative to absolute Beedbyte URLs, and line endings may differ; the mathematical and historical review wording is unchanged. Use [the unversioned publication page](https://beedbyte.tech/publications/three-arm-spider-zero-rotatability) for the current note, later revisions, and its proof archive; [Version 1](https://beedbyte.tech/publications/three-arm-spider-zero-rotatability/v/1) is the archived version represented here. The [project page](https://beedbyte.tech/research/graceful-spider-three-arms) gives a shorter overview.

## Check the certificates

Python 3 is sufficient; no third-party packages are required. From the repository root, run:

```sh
python proof/verify_proof.py
python proof/k4_verify.py
```

The first script checks the five zero-vertex types for `S(3,3,3,1^m)` against [`bases.json`](proof/bases.json). The second checks the six types for `S(4,4,4,1^m)` against [`k4_bases.json`](proof/k4_bases.json). Each script checks the exact vertex labels, the sorted edge differences, and the threshold interval condition for `m=1,...,100`. The programs do not replace the induction proof in the note.

## Scope and provenance

The repository records the two cases already published on Beedbyte. Work on arm length five is ongoing and is not part of this release. No claim is made for arbitrary spiders or other arm lengths. Publication priority for the two stated cases is unresolved; the note names related work and does not claim the general gap-insertion idea as new.

The research and checks were AI-assisted under School Scotty / Beedbyte, maintained by Jordi Gartner. The mathematical reviews are internal; there has been no external peer review or formal proof-assistant verification. The German and Chinese versions are AI-assisted translations awaiting human language review.

[`PUBLICATION-MANIFEST.json`](PUBLICATION-MANIFEST.json) records source paths and file hashes. [`TEST-REPORT.md`](TEST-REPORT.md) records the staging checks. No license has been selected for this repository yet.
