# Correction addendum — index 4 K29 source packet

This addendum corrects references and text in `report.md`. The original report remains byte-for-byte preserved at SHA-256 `81e75722dfdf469502076fe7e20201679e43c1fcbf3f7ed5f367897cb764aac7`; it must not be treated as the corrected text. This addendum is authoritative for filenames, hashes, and target-depth wording.

## Corrected result references

The exact K29 source literal is in [`result.json`](result.json), SHA-256 `af466f84614f492debfd28a396af2cddcaf2a2547d6efaa4605dbd341e544cf6`. Its zero indices are 3 and 4. Under the append indexing, index 3 gives depth 116 and index 4 gives depth 115 at K=119. These are separate selectable targets; each named arm and target uses its own whole-graph labeling. Reversing the source path gives the corresponding targets on the other named arm.

## Exact packet hashes

| File | SHA-256 |
|---|---|
| `criterion.md` | `f1b83c5c4d90cfc5d9d61ef25265b725cbf75be680a3e5b691cff683a49751c6` |
| `search.py` | `89c2b20ea7133ff83cfa4c48093726d5850c3ee94f3240658e250d8a30a58792` |
| `model.pbtxt` | `d8ccfff791bc90858756f0b70a294be260632635d61e51bd8a91670eab56d359` |
| `result.json` | `af466f84614f492debfd28a396af2cddcaf2a2547d6efaa4605dbd341e544cf6` |
| `check.py` | `91ed7c88e6242cd01f412e945322cfae71dd499d95975471dbba181c2bd9b011` |
| `normal.json` | `850af3a2a1ff652271528bd028669c1d898656861f499be0df5a31265fd988c4` |
| `optimized.json` | `850af3a2a1ff652271528bd028669c1d898656861f499be0df5a31265fd988c4` |

The normal and optimized checker outputs are byte-identical. The recorded single CP-SAT satisfaction attempt used OR-Tools 9.15.6755, random seed 0, 8 workers and a 120-second cap; it returned `OPTIMAL` in 4.384 seconds. A prior launch failed during API-level model construction before CP-SAT was invoked; the corrected script above was used for the sole solver attempt. No rerun was made after that solver attempt. `OPTIMAL` here records the solver's satisfaction status, not mathematical optimization or proof.

## Mathematical and review scope

The finite checker validates the complete source inventories, p90 append, K119 path labels and edge differences, and actual rooted-graph transfers for the singleton, one-edge, nononto triangle, and cyclic disconnected K4-plus-isolate residuals on both arms at depths 116 and 115 (16 graph cases, 3,848 edges). The all-r inference uses the frozen terminal-normalized append theorem referenced in the original packet. A separate blind reconstruction, Lean instantiation, external review, and worldwide-priority determination remain open. This packet is private and makes no public-release claim.
