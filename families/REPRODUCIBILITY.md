# Reproduction and extraction checks

Verified 9 October 2026 with Python 3.12. The package requires Python 3.10 or later and the standard library. Both checkers passed in this repository and after extracting a ZIP into a fresh temporary directory. The extracted run reproduced both result files byte-for-byte. The constructor, supplied checker, and six certificates match their original audited bytes; mathematical theorem and Sections 1–6 match the audited proof text. All prior files under `notes/`, `proof/`, and `k7/` remain byte-identical to the pre-packaging checkout.

Run from `families/`, or from the root of a ZIP containing these files:

```sh
python -B verify.py
python -B independent/verify_independent.py
```

These commands write `verification.json` and `independent/verification.json`; the extracted directory must be writable. Do not run the supplied assertion-based checker with Python optimization (`-O`); the independent checker uses explicit errors and remains active under optimization.

| Check | Supplied | Independent |
|---|---:|---:|
| Center formula | 1,440 | 5,376 |
| General odd-path formula | 100 | 200 |
| Certificates | 6 | 6 |
| Exact zero vertices, supplied constructor | 2,352 | 16,368 |
| Exact zero vertices, independent constructor | — | 16,368 |
| Representative complete labelings | 652 | — |
| Stress checks of both implementations | — | 208 |
| Rejected corruptions | 2 | 3 |

The independent checker also checks 6 and 5,040 restricted even-path permutations at k=2 and k=4. All checks passed. The two unbounded parameters are justified by the mathematical proof, not the test limits. This is a separate agent audit, not external expert review or formal proof verification.

To check hashes, compare each listed relative file against `SHA256SUMS.txt` using a SHA-256 tool before running scripts. The hash list covers every package file except itself. After a ZIP extraction, use these same commands from its extracted root; no external source directory, search code, network access, or installed solver is needed. Source hashes and disclosed editorial adaptations appear in `SOURCE-MANIFEST.json` and `SOURCE-README.md`.

## Proof ZIP snapshot and manuscript copies

The standalone proof ZIP is unchanged at SHA-256 `bb46e42b048de2d3bc4156ab68bf05eca17f18491c3b84e87c5fc92a5d1c98e6`; it contains the proof/checker package at commit `04c131d0b621b32f3c471c9e6b82b25ddbaac19f`. It excludes later `notes/` manuscript copies and documentation additions. Verify its included `SHA256SUMS.txt`, then run the same two commands above at the extracted root. This snapshot was freshly extracted and both checkers passed again when the three manuscript copies were added; the resulting JSON reports matched the current repository reports byte-for-byte. `notes/MANIFEST.json` supplies separate source/output hashes for the manuscript adaptations.

## Current five-length proof archive

The new `graceful-family-k11-public-proof.zip` contains `families/` with the independently audited `k11/` extension, excluding `families/notes/`. Extract it, enter its `families/` directory, and run all four commands below. Its included hash list covers the extracted proof-only files; the repository hash list additionally covers manuscript files. The earlier ZIP and manuscript provenance remain historical 3/5/7/9 snapshots.

```sh
python -B verify.py
python -B independent/verify_independent.py
python -B k11/check.py
python -B k11/independent/verify_independent.py
```

Both assertion-based checkers must run without `-O`; the independent checkers use explicit errors. K11's first checker validates four certificates, 1,680 exact-arm compositions, and two corrupt inputs. Its separate checker validates 84 center cases, 7,172 prescribed vertices, 48 stress compositions and three corrupt certificates/metadata cases. All four checkers passed again in the repository and after fresh archive extraction. Both generated result files matched between the repository and extracted archive byte-for-byte. The finite checks support transcription and implementation; the universal statement follows from the independently assessed argument, with priority unresolved and external mathematical review pending.
