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

## Two new arms on a rooted graceful graph

Let `H` be any finite graph with a supplied conventional graceful labeling whose
chosen root has label zero. Attach two distinct new `K`-edge arms there, retaining
all of `H`. The [all-even rooted source package](all-even-rooted-prefix/v1/README.md)
proves that, for every even `K≥20`, each depth `2..D8(K)` on either new arm can
separately receive zero in a conventional graceful labeling. The bound `D8` is
given explicitly in the package and grows without bound. Read the
[English](https://beedbyte.tech/publications/even-arm-rooted-graceful-zero-depths/v/1),
[German](https://beedbyte.tech/de/publications/even-arm-rooted-graceful-zero-depths/v/1),
or [simplified Chinese](https://beedbyte.tech/zh/publications/even-arm-rooted-graceful-zero-depths/v/1)
version of the article.

For the fixed length `K=95`, the [rooted interior source package](k95-rooted-residual/v1/README.md)
also covers each depth `1..94` on either new arm, with a separate labeling for
each target. Neither result asserts zero placements at the new tips or arbitrary
old vertices of `H`, or that every chosen root has a graceful zero labeling.
German and simplified Chinese package notes are draft translations. The
mathematical and copied-source checks are internal; exact worldwide priority
and external scholarly review remain unresolved.

## Even-arm terminal-12 seed windows

For any even terminal-12 seed satisfying the finite inventory and local-tag
conditions in the [versioned source package](even-q24-terminal-seed/v1/README.md),
two new arms of length `K=K0+24t` attached to a supplied graceful root-zero
graph have a separately zero-labelable vertex at every depth in
`[K0-z0-1+20t, K0-z0+22t]` on either named arm. The package includes literal
`K0=28` and `K0=30` cases and the precise `K0=30` overlap with the all-even
rooted prefix from `t=4`. This is conditional on a qualifying seed; it does
not assert such seeds for every even length, simultaneous zeros, old-graph
vertices, or tips. English is the source; German and simplified Chinese are
draft translations. The Lean and separate copied-source checks are internal,
and exact worldwide priority remains unknown.

## Fixed 25-edge arms

For every `n>=2,m>=0`, the center, every actual vertex on each named 25-edge arm, and every original named center leaf of `S(25^n,1^m)` can individually receive zero in a graceful labeling; the labeling may depend on the chosen vertex. The [fixed-k25 source package](fixed-k25/v1/README.md) has 27 byte-pinned Lean modules, a reproducible build, and [English](fixed-k25/v1/note.en.md), [German](fixed-k25/v1/note.de.md), and [simplified Chinese](fixed-k25/v1/note.zh.md) notes. German and Chinese are draft translations without documented human language review. `n=2,m=0` is `P51`; `n=2,m=1` is `P51` with a central leaf. Both cases have prior coverage, while worldwide priority for the full statement is **unknown**. A separate internal copied-source replay passed and is not external scholarly review. No PDF is supplied.
Read the [versioned Beedbyte article](https://beedbyte.tech/publications/zero-rotatability-25-edge-arm-spiders/v/1).

## Fixed 47-edge arms

For every `n≥2,m≥0`, each actual named vertex of `S(47^n,1^m)` can separately receive zero in a graceful labeling; the labeling may depend on the selected vertex. The [fixed-k47 source package](fixed-k47/v1/README.md) contains 42 byte-pinned Lean modules, a reproducible build, and [English](fixed-k47/v1/note.en.md), [German](fixed-k47/v1/note.de.md), and [simplified Chinese](fixed-k47/v1/note.zh.md) notes. German and Chinese are draft translations without documented human language review. The separate copied-source replay passed 42 fresh modules, theorem-closure and axiom checks, 191 named `n=2,m=0/1` instances, and six semantic negative controls; these are internal checks, not external scholarly review. The path cases `n=2,m=0/1` have prior coverage. Worldwide priority is **unknown**. This is fixed `k=47`, not an all-odd theorem. No PDF is supplied.
Read the [versioned Beedbyte article](https://beedbyte.tech/publications/zero-rotatability-47-edge-arm-spiders/v/1).

## Fixed 71-edge arms

For every `n>=2,m>=0`, each actual named vertex of `S(71^n,1^m)` can separately receive zero in a graceful labeling; the labeling may depend on the selected vertex. The [fixed-k71 source package](fixed-k71/v1/README.md) contains 45 byte-pinned Lean modules, a reproducible build, and [English](fixed-k71/v1/note.en.md), [German](fixed-k71/v1/note.de.md), and [simplified Chinese](fixed-k71/v1/note.zh.md) notes. German and Chinese are draft translations without documented human language review. The copied-source replay passed all 45 modules, 2,048 theorem closures, 503 named-target instances, and 12 semantic negative controls; this is internal checking, not external scholarly review. The path cases `n=2,m=0/1` have prior coverage. Worldwide priority is **unknown**. This is fixed `k=71`, not an all-odd theorem. No PDF is supplied.
Read the [versioned Beedbyte article](https://beedbyte.tech/publications/zero-rotatability-71-edge-arm-spiders/v/1).

## Fixed 95-edge arms

For every `n≥2,m≥0`, each actual vertex of `S(95^n,1^m)` can receive zero
in its own graceful labeling. The [fixed-k95 source package](fixed-k95/v1/README.md)
contains 35 byte-pinned Lean modules, a reproducible build, a complete depth
catalogue, and English, German and simplified Chinese notes. The German and
Chinese notes are draft translations without documented human language review.
Separate internal mathematical checks and a copied-source Lean replay passed;
these are not external review. Earlier path subfamilies overlap, and worldwide
priority remains unknown. The theorem concerns this fixed arm length.
Read the [versioned Beedbyte article](https://beedbyte.tech/publications/zero-rotatability-95-edge-arm-spiders/v/1).

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
labeling can put zero at that actual vertex. For `t≥1`, a terminal construction
also covers depth `21+22t`. Different targets may use different labelings.
At `k=47` this covers depths `37..43`, and at `k=71` depths `57..65`;
it does not assert all-vertex coverage at those lengths.

The [versioned Lean source package](q24-variable-window/v1/README.md) has
33 byte-pinned modules, a reproducible isolated build and [English](q24-variable-window/v1/note.en.md),
[German](q24-variable-window/v1/note.de.md) and [Chinese](q24-variable-window/v1/note.zh.md)
research notes. German and Chinese are draft translations without documented
human language review. A separate internal copied-source replay passed;
this is not external scholarly review. Earlier path subfamilies overlap,
and worldwide priority remains unknown. No PDF is supplied.
The additional terminal depth has its own [source package](q24-terminal-b1/v1/README.md)
with 34 byte-pinned Lean modules and separate internal mathematical and
copied-source checks.
Read the [versioned Beedbyte research note](https://beedbyte.tech/publications/prescribed-zero-window-equal-arm-spiders/v/3).

## q48 terminal zero positions

For `k=23+24t` with integer `t≥2`, all `n≥2,m≥0` and any named long arm
of `S(k^n,1^m)`, the [q48 source package](q48-two-flip/v1/README.md)
provides separate graceful labelings with zero at depths `21+22t` and
`22+22t`. It contains 36 byte-pinned Lean modules, a reproducible build,
mathematical checks and English, German and simplified Chinese notes.
The construction is terminal; it does not establish full zero-rotatability
throughout this progression. The package credits earlier path constructions;
worldwide priority remains unknown. The mathematical and copied-source Lean
checks are internal, and the language notes are drafts without recorded human
language review. For `t≥5`, the D8/q24 prefix (including B1) reaches `21+22t`;
adding this q48 depth extends the contiguous covered prefix to `1≤d≤22+22t`.
Read the v3 Beedbyte article in [English](https://beedbyte.tech/publications/prescribed-zero-window-equal-arm-spiders/v/3),
[German](https://beedbyte.tech/de/publications/prescribed-zero-window-equal-arm-spiders/v/3),
or [simplified Chinese](https://beedbyte.tech/zh/publications/prescribed-zero-window-equal-arm-spiders/v/3).

## Two arms attached to a rooted graceful graph

For each integer `t≥1`, set `K=23+24t`, `d₀=20+22t` and `d₁=21+22t`.
Start with any finite conventionally graceful graph `H` whose selected root
has label zero, then attach two named `K`-edge arms there while retaining all
of `H`. Each arm separately admits zero at either specified depth, using
four separate labeling witnesses. Vertex labels of `H` need only be injective
into `0,…,Q`, where `Q` is its edge count; no tree, connectivity, alpha-labeling
or vertex-onto assumption is required. Old vertices of `H`, new tips and other
depths are outside this statement.

The [q24 rooted-residual source package](q24-rooted-residual/v1/README.md)
contains 60 byte-pinned Lean modules, a reproducible build and three reader
notes. It credits the established alpha/graceful amalgamation and high-side
shift described by Barrientos (2022). Worldwide priority remains unknown;
the mathematical and Lean checks are internal, not external peer review.
German and Chinese remain translation drafts awaiting language review.
Read the versioned Beedbyte article in [English](https://beedbyte.tech/publications/prescribed-zero-positions-rooted-graceful-graft/v/1),
[German](https://beedbyte.tech/de/publications/prescribed-zero-positions-rooted-graceful-graft/v/1),
or [simplified Chinese](https://beedbyte.tech/zh/publications/prescribed-zero-positions-rooted-graceful-graft/v/1).

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
