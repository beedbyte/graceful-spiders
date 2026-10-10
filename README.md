# Beedbyte graceful spiders

## All even arm lengths

For every even `k≥2`, all `n≥2,m≥0`, and each actual named vertex of
`S(k^n,1^m)`, a graceful labeling can put zero at that vertex. Different
requests may use different labelings. The [versioned result package](all-even-ge2/v1/README.md)
contains the English manuscript source, three article presentations and the
186-module Lean source build. The German and Chinese texts are draft translations;
PDF compilation and rendered layout remain unverified. Internal checks are not
external peer review, and worldwide priority is unresolved.
Read the [versioned Beedbyte article](https://beedbyte.tech/publications/zero-rotatability-even-arm-spiders/v/1).

## Fixed 25-edge arms

For every `n>=2,m>=0`, the center, every actual vertex on each named 25-edge arm, and every original named center leaf of `S(25^n,1^m)` can individually receive zero in a graceful labeling; the labeling may depend on the chosen vertex. The [fixed-k25 source package](fixed-k25/v1/README.md) has 27 byte-pinned Lean modules, a reproducible build, and [English](fixed-k25/v1/note.en.md), [German](fixed-k25/v1/note.de.md), and [simplified Chinese](fixed-k25/v1/note.zh.md) notes. German and Chinese are draft translations without documented human language review. `n=2,m=0` is `P51`; `n=2,m=1` is `P51` with a central leaf. Both cases have prior coverage, while worldwide priority for the full statement is **unknown**. A separate internal copied-source replay passed and is not external scholarly review. No PDF is supplied.
Read the [versioned Beedbyte article](https://beedbyte.tech/publications/zero-rotatability-25-edge-arm-spiders/v/1).

## Fixed 47-edge arms

For every `n≥2,m≥0`, each actual named vertex of `S(47^n,1^m)` can separately receive zero in a graceful labeling; the labeling may depend on the selected vertex. The [fixed-k47 source package](fixed-k47/v1/README.md) contains 42 byte-pinned Lean modules, a reproducible build, and [English](fixed-k47/v1/note.en.md), [German](fixed-k47/v1/note.de.md), and [simplified Chinese](fixed-k47/v1/note.zh.md) notes. German and Chinese are draft translations without documented human language review. The separate copied-source replay passed 42 fresh modules, theorem-closure and axiom checks, 191 named `n=2,m=0/1` instances, and six semantic negative controls; these are internal checks, not external scholarly review. The path cases `n=2,m=0/1` have prior coverage. Worldwide priority is **unknown**. This is fixed `k=47`, not an all-odd theorem. No PDF is supplied.
Read the [versioned Beedbyte article](https://beedbyte.tech/publications/zero-rotatability-47-edge-arm-spiders/v/1).

## Fixed 23-edge arms

For every `n≥2,m≥0`, each actual named vertex of `S(23^n,1^m)` can separately
receive zero in a graceful labeling. The [fixed-k23 source package](fixed-k23/v1/README.md)
contains 27 byte-pinned Lean modules, an English research note and German and
simplified Chinese draft translations. A separate internal copied-source replay
compiled all 27 modules and checked the theorem closures; it is not external
scholarly review. The `n=2,m=0/1` path cases have earlier coverage. The full
Cattell construction remains unassessed for the simultaneous path anchors used
here, so worldwide priority is unknown. No PDF is supplied.
Read the [versioned Beedbyte article](https://beedbyte.tech/publications/zero-rotatability-23-edge-arm-spiders/v/1).

## Variable q24 zero-depth interval

For arm lengths `k=23+24t` with integer `t≥0`, all `n≥2,m≥0`, any named
long arm of `S(k^n,1^m)` and every depth `17+20t≤d≤20+22t`, a graceful
labeling can put zero at that actual vertex. Different targets may use
different labelings. At `k=47` this covers depths `37..42`, and at `k=71`
depths `57..64`; it does not assert all-vertex coverage at those lengths.

The [versioned Lean source package](q24-variable-window/v1/README.md) has
33 byte-pinned modules, a reproducible isolated build and [English](q24-variable-window/v1/note.en.md),
[German](q24-variable-window/v1/note.de.md) and [Chinese](q24-variable-window/v1/note.zh.md)
research notes. German and Chinese are draft translations without documented
human language review. A separate internal copied-source replay passed;
this is not external scholarly review. Earlier path subfamilies overlap,
and worldwide priority remains unknown. No PDF is supplied.
Read the [versioned Beedbyte research note](https://beedbyte.tech/publications/prescribed-zero-window-equal-arm-spiders/v/1).

## Prescribed-zero prefixes

For every integer arm length `k≥19`, all `n≥2,m≥0`, any selected long arm
of `S(k^n,1^m)` and each depth `2≤d≤D8(k)`, a graceful labeling can put zero
at the requested vertex. Different requests may use different labelings.
Both arm-length parities and the path boundary `n=2,m=0` are included.
The sufficient prefix has limiting proportion `10/11`.

The [prefix package](prescribed-zero-prefix/v1/README.md) gives the piecewise
bound, written construction, certificates, executable checks, Lean source
proof and separate copied-source replay. For `k≥125`, write
`p=floor((k−3)/2)=61+11a+r`, `0≤r≤10`; then `D8(k)=107+20a+2r`.
The bound `0≤10k−11D8(k)≤261` holds through all integer lengths.
Read the [manuscript](prescribed-zero-prefix/v1/manuscript.md), its shorter
[German](prescribed-zero-prefix/v1/manuscript.de.md) and
[Chinese](prescribed-zero-prefix/v1/manuscript.zh.md) presentations, and the
[verification scope](prescribed-zero-prefix/v1/verification-scope.md).
This is sufficient coverage, without an assertion of full zero-rotatability,
optimality or historical priority. Internal checks do not constitute external
peer review. Formal ratio verification uses an integer precision criterion.

## Earlier constructions

The [three-arm source records](PUBLICATION-MANIFEST.json) and [K7 package](k7/README.md) retain their
earlier certificate constructions for exactly three long arms and `m≥1`.
The [equal-arm family package](families/README.md) covers all vertices for
`k∈{3,5,7,9,11}`, `n≥2,m≥0`, together with its stated partial odd-length
results. The [growing-depth package](growing-depth/v1/README.md) retains its
separate formula at depths `4s,4s+1`, for `s≥1,r≥3s,r≠3s+1,k=2r+1`.
Its [proof ZIP](growing-depth/v1/graceful-growing-depth-v1.1-proof.zip) and
all earlier source files remain immutable. These earlier packages retain
their own verification scope; the new prefix package supplies the stated
formal proof. Classical ingredients and prior authors are credited in the
linked source comparisons. No repository license has been selected.

## Publication and methods

Jordi Gartner publishes this work through Beedbyte. The
[package methods](prescribed-zero-prefix/v1/README.md) document specific AI
assistance in construction, proof, computation, formalization, source comparison
and draft language work. German and Chinese presentations have no documented
human language review. The [Beedbyte research note](https://beedbyte.tech/publications/growing-prescribed-zero-depths-equal-arm-spiders)
provides the versioned website presentation and earlier revisions.

[PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json),
[TEST-REPORT.md](TEST-REPORT.md) and
[K7 reproduction manifest](k7/REPRO-MANIFEST.json) remain records of their
original packages. Their historical README hashes identify earlier versions.
