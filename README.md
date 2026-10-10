# Beedbyte graceful spiders

## All even arm lengths

For every even `k≥2`, all `n≥2,m≥0`, and each actual named vertex of
`S(k^n,1^m)`, a graceful labeling can put zero at that vertex. Different
requests may use different labelings. The [versioned result package](all-even-ge2/v1/README.md)
contains the English manuscript source, three article presentations and the
186-module Lean source build. The German and Chinese texts are draft translations;
PDF compilation and rendered layout remain unverified. Internal checks are not
external peer review, and worldwide priority is unresolved.

## Fixed 23-edge arms

For every `n≥2,m≥0`, each actual named vertex of `S(23^n,1^m)` can separately
receive zero in a graceful labeling. The [fixed-k23 source package](fixed-k23/v1/README.md)
contains 27 byte-pinned Lean modules, an English research note and German and
simplified Chinese draft translations. A separate internal copied-source replay
compiled all 27 modules and checked the theorem closures; it is not external
scholarly review. The `n=2,m=0/1` path cases have earlier coverage. The full
Cattell construction remains unassessed for the simultaneous path anchors used
here, so worldwide priority is unknown. No PDF is supplied.

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
