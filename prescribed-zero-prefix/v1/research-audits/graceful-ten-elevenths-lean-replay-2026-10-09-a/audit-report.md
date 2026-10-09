# D7 separate internal copied-source Lean replay

9 October 2026. **GO for the exact all-integer actual-spider D7 prefix,
K7 inverse relative to D7, nonregression, monotonicity, q11/core construction
and integer ratio criterion.** No blocking discrepancy was found. This is an
internal project check assisted by AI in artifact checking, source inspection,
compilation and negative controls, not external review or scholarly peer review.
Jordi Gartner publishes the work through Beedbyte. No public CMS, site, profile
or shared checkpoint was changed.

## Input identity and isolated replay

The frozen author package is `../graceful-ten-elevenths-formal-2026-10-09-a`.
Its manifest SHA256 is
`76022dcd140c9a989040d7c25e8ed597336d0971739066ad95e7983c129bdcec`;
its report SHA256 is
`8217316adc5e4174eebb6a145cbfe98795c84433957a1d9ee5a824cdba33b283`.
All 289 author manifest entries and full payload coverage were verified before
and after replay. Every copied source/input hash and every bound original
input/predecessor manifest/payload hash was also checked. Author bytes remain
unchanged; no build or checker was executed in the author package.

This new directory contains exact copied source and binding inputs, with no
copied author build directories. All 52 modules compile with zero exit codes
and `-DwarningAsError=true` in the previously absent `build-replay`. Its isolated
`LEAN_PATH` contains only that fresh directory. No author object file supplies
a local import. Source hashes were checked around each compiler call; fresh
commands, logs, timings and toolchain identity are preserved. Copied author
`report.md`, `README.md`, `verification.json` and inventories retain their
original meanings. This report and `replay-verification.json` are the separate
audit evidence; `AUTHOR-SHA256SUMS.txt` preserves the original manifest.

## Exact principal scope

Inspected `Q11Depth.lean`, `Q11Prefix.lean`, `Q11Recipes.lean`, the q11 gadget,
and the fresh principal theorem output in `build-replay/Q11Audit.log`.
`GracefulBoundary.Q11.all_lengths_prefix_zero` states:

```lean
theorem all_lengths_prefix_zero (k n m d : Nat) (hk : 19≤k)
    (hn : 2≤n) (a : Fin n) (hd : 2≤d ∧ d≤depthPrefix k) :
    ∃ (hlt : d-1<k) (f : SpiderVertex n m k → Nat),
      Graceful (spiderGraph n m k) (n*k+m) f ∧ f (.arm a ⟨d-1,hlt⟩)=0
```

D7 equals D6 for k≤124. For k≥125, p=floor((k-3)/2) and
D7(k)=F(p)=107+20 floor((p-61)/11)+4 floor(min((p-61) mod 11,9)/2).
D6 is 11 through k34, 27 through k52, and 25+16 floor((k-35)/18) afterward.
Every natural k≥19, n≥2, m≥0, chosen arm and depth 2≤d≤D7(k) is quantified.
There is no parity restriction or finite upper bound. The legal vertex index is
d-1. Separate prescribed vertices may use different labelings.

The inherited exact `SpiderVertex`/`spiderGraph` definitions comprise the center,
n arms of k vertices and m single-edge leaves, with each arm joined successively
from the center. `Graceful` means a full bijection onto vertex labels 0..n*k+m
and actual absolute endpoint differences 1..n*k+m. These are the frozen graph
contracts checked in the preceding D5/D6 replays and copied identically here.
Odd and even generic transfers discharge the final graph premises. No supplied
core, residual-gracefulness hypothesis or graph-identification assumption remains
in the principal declaration.

K7(d)=K6(d) for d≤89; for d≥90 it is
125+22 floor((d-104)/20)+4 floor(((d-104) mod 20)/4), using truncated natural
subtraction. `cutoff_covers`, `cutoff_previous_fails`, monotonicity and
`cutoff_minimal` establish the exact inverse **relative to displayed D7** for
d≥2 and candidate lengths k≥19. The failed previous-length condition is only
required when that length is in the k≥19 domain. This is not a least length
among all graceful labelings. `all_lengths_eventual_zero` gives the same actual
spider conclusion at every k≥K7(d). `prefix_inside` and `cutoff_depth_bound`
establish the legal depth bounds.

`prefix_error_bound` proves both 11D7(k)≤10k and 10k-11D7(k)≤261 for all k≥19;
natural subtraction therefore cannot mask a negative error. The unbounded
integer precision criterion uses cutoff 262*precision+19 and both parities.
A literal real-number/topological Tendsto theorem or formal equivalence to the
integer criterion is absent.

## Proof and inventory checks

The q11 literal certificate is P=[3,8],
B=[11,10,5,5,4,2,3,4], D=[1,1,2,6,6,7,7,9,10,8,9,11]. Its finite side/chain
proofs use ordinary kernel `decide`. The insertion preserves the full anchored
core contract and tracked maximum pair. The reflected step gives size +11,
depth +20. Recipes combine q11 and q9 moves before transformation and C6 growth
after transformation. The six base rows and eleven bridge rows are finite
recipe certificates linked to universal core-construction proofs.

Strong induction supplies every core size p≥61: C6 growth covers the earlier
interval and translated bridge recipes cover the remainder. The low depths use
the proved D6 core bound. The 99-residue finite nonregression certificate and
the +99 shift comparison supply the unbounded D6 comparison. No finite search
status or Python recipe calculation is a Lean proof premise.

`replay_check.py` independently reconstructs namespace-qualified source theorem
names and parses the fresh all-theorem output. All 658 names match the frozen
inventory. Every one of the 658 explicit axiom reports occurs exactly once and
its full dependency list matches the frozen inventory. The sole dependency
union is `propext`, `Classical.choice`, `Quot.sound`; principal dependency lists
are individually preserved in `replay-verification.json`. There is no
nonstandard mathematical axiom or `sorryAx` in those reports.

The comment/string-aware lexical scan finds no `sorry`, `admit`, `native_decide`,
`sorryAx`, `axiom` or `unsafe` code token. All 52 sources are covered and `Std` is
the sole external source import. The query module itself is freshly rebuilt.

## Negative source and hash-drift controls

Two focused source copies retain their actual imports, definitions and relevant
certificate proofs while excluding later users. In the gadget control, changing
P's first entry 3→4 breaks the inserted sum certificate and H3 boundary. In the
recipe control, changing the sole p61 base recipe's q9 count 5→4 breaks exact
size/depth coverage. Both are rejected by ordinary `decide` with false
propositions and nonzero compiler exits, under the same warnings-as-errors
toolchain and fresh replay imports. These failures are mathematical certificate
defects, not missing-import or syntax-error tests.

A third separate copy appends one newline to `Q11Depth.lean`. The recorded
source-identity equality gate rejects that semantically harmless byte drift.
Original expected and mutated hashes, commands, exit codes and compiler
diagnostics are saved in `negative-controls/`. Positive replay sources and
original author records remain unchanged.

## Trust and freeze boundaries

Lean 4.34.0 Windows x86_64 release commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` is used, compiler SHA256
`a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`.
The compiler/kernel and installed Std remain trusted and were not independently
rebuilt or externally certified. This audit confirms source replay and scope
relative to those components and standard axioms. It does not establish
historical novelty, global graph-theoretic optimality, full zero-rotatability,
restricted-recipe maximality, unequal arms, unrestricted even depth one,
near-tip completeness, new rooted-graft results or D8.

The new local `SHA256SUMS.txt` binds every audit payload except itself. Verify
frozen bytes read-only with `python -B freeze_audit.py --verify`. Reproduce in
another fresh copy; do not rebuild or regenerate inside this frozen record.
