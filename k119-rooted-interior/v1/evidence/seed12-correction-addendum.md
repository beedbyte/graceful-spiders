# Correction addendum — index 2 K29 source packet

This addendum corrects references and text in `report.md`. The original report remains byte-for-byte preserved at SHA-256 `1d5d73086b11d0e885be86b2076e4a91c7588970ea7e36d168c1b3da40dd9d38`; it must not be treated as the corrected text. This addendum is authoritative for filenames, hashes, and target-depth wording.

## Corrected result references

The exact K29 source literal is in [`result.json`](result.json), SHA-256 `0d8b0c0164b98fcd3e28ee7d95016cd43aa4d7355c9ad94ff0fe317ab4bf9e93`. Its zero indices are 1 and 2. Under the append indexing, index 1 gives depth 118 and index 2 gives depth 117 at K=119. These are separate selectable targets; each named arm and target uses its own whole-graph labeling. Reversing the source path gives the corresponding targets on the other named arm.

## Exact packet hashes

| File | SHA-256 |
|---|---|
| `criterion.md` | `fbd040bd580f33f7859535423aa8b2355d40066ab6860fb7f507b48a6870beb1` |
| `search.py` | `acb0e8a6c6b509710eef3556a74e8b93f2968db80583340dc58dfc34c5de5966` |
| `model.pbtxt` | `6953f4d05b2c2bbb23ce8cb55b6ae6adba3c7f70b250e9fa88d44e42ec909099` |
| `result.json` | `0d8b0c0164b98fcd3e28ee7d95016cd43aa4d7355c9ad94ff0fe317ab4bf9e93` |
| `check.py` | `ceccce2cc4dea25b83ea0528b2e0da98171f936bbeb124d4064ae09dd5c5dfb14` |
| `normal.json` | `8bb09cabbfbeb47939366bac870d586c02cb20de128d7b69de452c4d3646f5e8` |
| `optimized.json` | `8bb09cabbfbeb47939366bac870d586c02cb20de128d7b69de452c4d3646f5e8` |

The normal and optimized checker outputs are byte-identical. The recorded single CP-SAT satisfaction attempt used OR-Tools 9.15.6755, random seed 0, 8 workers and a 120-second cap; it returned `OPTIMAL` in 4.760 seconds. A prior launch failed during API-level model construction before CP-SAT was invoked; the corrected script above was used for the sole solver attempt. No rerun was made after that solver attempt. `OPTIMAL` here records the solver's satisfaction status, not mathematical optimization or proof.

## Mathematical and review scope

The finite checker validates the complete source inventories, p90 append, K119 path labels and edge differences, and actual rooted-graph transfers for the singleton, one-edge, nononto triangle, and cyclic disconnected K4-plus-isolate residuals on both arms at depths 118 and 117 (16 graph cases, 3,848 edges). The all-r inference uses the frozen terminal-normalized append theorem referenced in the original packet. A separate blind reconstruction, Lean instantiation, external review, and worldwide-priority determination remain open. This packet is private and makes no public-release claim.
