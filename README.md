# Graceful spider trees: prescribed-zero constructions

This repository contains certificate proofs of prescribed-zero gracefulness: the original three-arm notes for `k ∈ {3,4}` and `k=7`, a full prescribed-zero family for `S(k^n,1^m)` with `k ∈ {3,5,7,9,11}`, and a growing partial set of zero depths for odd `k ≥ 11`. The family statements allow arbitrary integers `n ≥ 2` and `m ≥ 0`. The written arguments establish their stated unbounded parameter ranges; finite checks verify certificates and implementations.

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

## Equal-arm families: arbitrary arm and leaf counts

The [family package](families/README.md) proves zero-rotatability of `S(k^n,1^m)` for `k ∈ {3,5,7,9,11}`, `n ≥ 2`, and `m ≥ 0`, including the path boundary `n=2,m=0`. The unchanged 3/5/7/9 proof uses six alpha-path certificates; the [independently audited k11 extension](families/k11/README.md) adds four more. Both use established center-zero, alpha-amalgamation, and leaf-extension constructions. It also gives selected zero positions for every odd `k ≥ 3`; it does not prove full zero-rotatability for all odd lengths.

Full manuscript copies of the independently checked five-length theorem: [English](families/notes/article.en.md), [Deutsch](families/notes/article.de.md), and [中文](families/notes/article.zh.md). Their [source manifest](families/notes/MANIFEST.json) records approved hashes and relative-link adaptations.

Read the [proof](families/proof.md), [separate agent audit](families/independent/AUDIT.md), [literature comparison](families/literature.md), and [source provenance](families/SOURCE-README.md). Python 3.10 or later and the standard library are sufficient:

```sh
python -B families/verify.py
python -B families/independent/verify_independent.py
python -B families/k11/check.py
python -B families/k11/independent/verify_independent.py
```

Known overlaps include all path cases, two long arms with one center leaf, `k=3,n=2` with arbitrary center leaves, and uniform three-edge arms. Ordinary gracefulness of the entire family is already known. Publication priority is unresolved; no novelty or first-proof claim is made. The audit used a separately implemented checker in another agent review, and is not external peer review.

## Growing prescribed-zero depths

The [Beedbyte research note](https://beedbyte.tech/publications/growing-prescribed-zero-depths-equal-arm-spiders) gives the current English, German, and Chinese presentation and links its earlier versions. The proof package below remains the fixed research source for that note; later website copy revisions do not change its theorem or files.

The [versioned construction](growing-depth/v1/README.md) supplies a growing partial set of zero depths in equal-arm spiders. For integers `s>=1`, `r>=3s`, `r!=3s+1`, `k=2r+1`, all `n>=2,m>=0`, and every specified long-arm vertex at depth `4s` or `4s+1`, a separate graceful labeling gives that vertex zero. For every odd `k>=11`, at least `2 floor((k-5)/6)` depths are guaranteed. The earlier all-vertex theorem for `k in {3,5,7,9,11}` retains its own scope.

Read the [proof](growing-depth/v1/source/proof.md), [independent internal AI-agent audit](growing-depth/v1/reviews/independent/audit-report.md), [source comparison](growing-depth/v1/reviews/prior-art-report.md), and notes in [English](growing-depth/v1/notes/article.en.md), [Deutsch](growing-depth/v1/notes/article.de.md), and [中文](growing-depth/v1/notes/article.zh.md). The [proof archive](growing-depth/v1/graceful-growing-depth-v1.1-proof.zip) contains this version's source and review files. The unbounded statement follows from the proof; finite checks support implementation. This is partial coverage, with unresolved historical priority and no external peer review or proof-assistant verification.

## Scope and provenance

The earlier three-arm notes establish their stated families for `m ≥ 1`. The family package proves full prescribed-zero coverage for exactly `k ∈ {3,5,7,9,11}`, `n ≥ 2`, `m ≥ 0`, plus its stated partial odd-length result. The growing-depth package proves additional partial coverage at the depths and parameters it names. These arguments do not establish arbitrary spiders or full zero-rotatability at other arm lengths. No theorem or method priority is claimed. The K7 note has no assigned DOI or canonical citation.

The research and checks were AI-assisted under School Scotty / Beedbyte, maintained by Jordi Gartner. The mathematical reviews are internal; there has been no external peer review or formal proof-assistant verification. The German and Chinese versions are AI-assisted translations awaiting human language review.

[PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json) and [TEST-REPORT.md](TEST-REPORT.md) record the original k=3/4 staging provenance and checks; their historical README hash refers to the earlier README. [The K7 reproduction manifest](k7/REPRO-MANIFEST.json) records the K7 source data. No license has been selected for this repository yet.
