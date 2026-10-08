# K7 reproduction checks

Run date: 9 October 2026. Runtime: Python 3.12.1; minimum Python 3.10. Only the standard library is required. Both checkers were run from the repository's `k7/repro/` directory and returned status zero.

From the repository root:

```sh
cd k7
cd repro
python research-audits/graceful-k7-feasibility/verify-continuation.py
python research-audits/graceful-k7-independent/independent_check.py
```

After extracting the proof archive, start in its extracted root with `cd repro`, then run the two Python commands.

The first checker verified nine zero-label orbits, exact affine formulas, threshold intervals, a reduced tip witness, the cut obstruction, and 900 labelings for m=1,...,100. The independent checker verified all nine orbits with exact all-n affine certificates, 54 explicit extensions, and 74 transports of zero to every vertex for m=1,2,5. Its odd-arm reduction, k=1 boundary, cut obstruction and deliberate corruption controls passed. It reported 5,913 candidate edge sets, 975 graceful trees, 6,189 valid invariant configurations, 18,567 insertions and 5,214 complements in its small-tree diagnostics. Its final message was `GO for mathematical statement; novelty not assessed.`

Finite diagnostics detect coding or transcription mistakes. The infinite theorem follows from the written interval proof and complete nine-orbit certificates. The separate implementation is internal checking; it is not external peer review or proof-assistant verification.

The nine reproduction files match the manifest before and after checker execution. The independent checker writes audit-results.json beside its source and requires write access. The ZIP contains exactly those nine files under repro/research-audits/. Its size is 23,708 bytes and its SHA-256 is `f5bc44be564bdf7e2c3ad648e023c03ebd203c52873c35cb76c6e156cad0048e`. Every ZIP member hash matches its manifest entry.

Historical partial/UNKNOWN statements in the unchanged feasibility README are source provenance. continuation.md and the independent audit establish the complete nine-orbit result and supersede those partial statements. No third-party papers are bundled.

The English, German and Chinese certificate and edge-difference tables were checked against the source JSON during preparation. All new relative links in the repository README, K7 notes and sources resolve to existing files. The German and Chinese texts are AI-assisted translations awaiting human language review. Publication priority remains unresolved, and no priority or license decision is implied by these checks.
