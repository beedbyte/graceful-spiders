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
