# Graceful spider trees with three equal long arms

This repository contains separate certificate notes for spider trees `S(k,k,k,1^m)`: one for `k ∈ {3,4}` and a K7 addition for `k=7`, each with integer `m ≥ 1`. Each note proves that every chosen vertex can receive label zero in some graceful labeling. The written constructions establish all `m`; finite computer checks verify the certificate data and detect transcription errors.

## Published note: arm lengths three and four

- [English](notes/paper.en.md)
- [Deutsch](notes/paper.de.md)
- [中文](notes/paper.zh.md)

These files are GitHub-readable copies of the public Version 1 note. Their project-page links were changed from site-relative to absolute Beedbyte URLs, and line endings may differ; the mathematical and historical review wording is unchanged. Use [the unversioned publication page](https://beedbyte.tech/publications/three-arm-spider-zero-rotatability) for the current note, later revisions, and its proof archive; [Version 1](https://beedbyte.tech/publications/three-arm-spider-zero-rotatability/v/1) is the archived version represented here. The [project page](https://beedbyte.tech/research/graceful-spider-three-arms) gives a shorter overview.

Python 3 is sufficient for the k=3 and k=4 checks; no third-party packages are required. From the repository root, run:

```sh
python proof/verify_proof.py
python proof/k4_verify.py
```

The first script checks the five zero-vertex types for `S(3,3,3,1^m)` against [bases.json](proof/bases.json). The second checks the six types for `S(4,4,4,1^m)` against [k4_bases.json](proof/k4_bases.json). Each script checks the exact vertex labels, sorted edge differences, and threshold interval condition for `m=1,...,100`. The programs do not replace the induction proof in the note.

## K7 addition: arm length seven

Read the [K7 publication on Beedbyte](https://beedbyte.tech/publications/seven-edge-three-arm-spider-zero-rotatability) for the website note and its archived versions.

- [English manuscript](k7/notes/manuscript.en.md)
- [Deutsch](k7/notes/paper.de.md)
- [中文](k7/notes/paper.zh.md)
- [Sources and coverage](k7/SOURCES.md)
- [Reproduction manifest](k7/REPRO-MANIFEST.json)
- [Proof archive](k7/graceful-k7-zero-rotatability-proof.zip)

For every integer `m ≥ 1`, `S(7,7,7,1^m)` is 0-rotatable. Five explicit base labelings and four complements cover its nine vertex orbits. A leaf-insertion lemma extends the certificates to every `m`. The accompanying source comparison distinguishes this prescribed-zero claim from prior gracefulness and α-gracefulness results; publication priority remains unresolved.

With Python 3.10 or later, run from the repository root:

```sh
cd k7
cd repro
python research-audits/graceful-k7-feasibility/verify-continuation.py
python research-audits/graceful-k7-independent/independent_check.py
```

Only the Python standard library is required. After extracting the archive into a separate directory, start at that extracted root with `cd repro` and run the same two Python commands. The independent checker writes `audit-results.json` beside its source, so that directory needs write access. The original reproduction layout and all nine manifest-listed files are preserved.

## Scope and provenance

The notes establish exactly the stated families for `m ≥ 1`. They do not establish `m=0`, arbitrary spiders, other arm lengths, or arbitrary numbers of long arms. No theorem or method priority is claimed. The K7 note has no assigned DOI or canonical citation.

The research and checks were AI-assisted under School Scotty / Beedbyte, maintained by Jordi Gartner. The mathematical reviews are internal; there has been no external peer review or formal proof-assistant verification. The German and Chinese versions are AI-assisted translations awaiting human language review.

[PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json) and [TEST-REPORT.md](TEST-REPORT.md) record the original k=3/4 staging provenance and checks; their historical README hash refers to the earlier README. [The K7 reproduction manifest](k7/REPRO-MANIFEST.json) records the K7 source data. No license has been selected for this repository yet.
