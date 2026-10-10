# Terminal q24 reversed-zero adapter: additive Lean author packet

10 October 2026. **Author formal GO for the scoped theorem; independent copied-source Lean replay remains pending.** This private packet proves the terminal B1/D23/A24 adapter and its actual named-spider transfer for every `t≥1`. It changes no frozen predecessor or public artifact.

## Principal theorem

`GracefulBoundary.Q24Terminal.terminal_actual` states that for every `t≥1`, `n≥2`, `m≥0`, and chosen `a : Fin n`, the actual graph `spiderGraph n m (23+24*t)` has separate graceful labelings placing zero at its named arm vertex of depth `20+22*t` and at the vertex of depth `21+22*t`. The result is expressed through `P20Q24.DepthZero`, whose witness contains the actual `SpiderVertex.arm a ⟨d-1,...⟩`, a full `Graceful` labeling with vertex range `0..n*(23+24*t)+m`, and all edge weights `1..n*(23+24*t)+m`. No m leaf or second arm is silently deleted; the theorem includes `n=2,m=0`.

`generic_source` proves the single final-step interface for **any** old `P20Q24.State k z c` with `k=2*p+3`. Its output `extend z c` has a `GenericPathCertificate (p+12)` at the true new midpoint, with decoded maximum at index `z+1` and zero at index `z+2`. The generic `extend_sides`, `extend_sums`, `extend_length`, `extend_midpoint`, and `extend_zeros` discharge the full high/low inventories, sums, size, midpoint, and reversed extreme positions. The proof uses the accepted old B2 state only as input; it does not claim the reversed output satisfies that input state or can be iterated.

`flip_certificate` instantiates the generic inventory through the existing unbounded `P20Q24.all_states s` (`k=23+24*s`, `z=3+2*s`). `flip_actual` applies the accepted `FiniteAlpha.prescribed_zero` theorem to the decoded path at length `47+24*s`, obtaining zero at depths `42+22*s` and `43+22*s` on every selected named arm, all `n≥2,m≥0`. Setting `t=s+1` yields the principal theorem. The upper target comes from a decoded maximum and whole-graph complement in the imported transfer; the lower target is directly zero. These are separate labelings.

The fixed gadget is exactly `B=[16]`, `D=[1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,9,9,11,21,24,24,23,23]`, and `A=[14,15,15,10,12,16,10,13,8,11,13,14,17,17,18,18,19,19,20,20,22,22,21,12]`. `prepare.py` parses the Lean lists and checks them elementwise against the frozen `data.json`. Kernel `decide` proves the fresh high side (`highs D ++ lows A`), fresh low side (`highs B ++ lows D ++ highs A`), and all three local sum chains as `1..50` exactly. The old nonzero sums translate by 48 to `51..2(k+24)-1`; the new zero edge supplies 0. All algebraic list lemmas are universal in the input `State`, not finite extrapolations in t.

## Frozen sources and scope

- Author mathematical report SHA-256 `469a6167c41653138a227527d6e56f8c229133df71ce63446fad1d5f153ac729`, literal `data.json` SHA-256 `8cc56a9ba7a0b9d062ef5d0035e5e6b889671e415ed7c586bfaa90f0427da57d`, manifest SHA-256 `1903408ad6d5a2e23917236912b76d1450e11a9455a322006a53b644b887fa0f`.
- Independent mathematical QA report SHA-256 `efc0e5ee50b6e214c81396d8523c8fc5fd84e99c9d28e0f488fbc49a6c57ed1e`, manifest SHA-256 `630514de88c00d69a29ce2fa0e7fcf03d0d1258bec80ba570f5253340ce76c75`. This is internal QA, not external or peer review.
- The 33 imported Lean sources are byte-identical copies from the frozen q24 variable-window formal author package (source index SHA-256 `e7108afaea7ef74cb5ab7c596925a3a22bb6b07ceff8e4721220dbc09a0e77f0`, report SHA-256 `392eecf6bceae9282121e9ba0753b79d33ee4061c4a1ee75377fd36df4ee4610`). Its separate copied-source replay report SHA-256 is `44a2d5b096d473102fbc3ec6936eba48bc8eb19391e68042ab6b8244d46f50a7`. All eight input pins are checked before copying/building.

The theorem supplies these two depths only. For `t≥5`, external previously proved D8/q24 prefix results make the upper depth one extra contiguous position; that union is mathematical context and is **not** a new Lean theorem in this packet. No full-k95, full-odd, or next-depth claim is made. Alpha amalgamation and related append operations have older antecedents; the exact terminal adapter's worldwide priority is **UNKNOWN**.

## Fresh verification

`python build.py` compiled all 34 sources from an absent OLEAN directory under `-DwarningAsError=true`, with `LEAN_PATH` pointing only to that fresh directory. The 33 predecessor OLEAN hashes reproduce the frozen author build exactly. Lean executable SHA-256: `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`.

`python checks.py` checked the principal type, **18 new theorem axiom closures**, concrete actual named cases `(t,n,m,a)=(1,2,0,0),(1,2,1,1),(2,2,0,1),(5,3,2,2)`, and six effective false-proposition mutants. The closures use only `propext`, `Classical.choice`, `Quot.sound` or subsets. Mutants change B, high-zero position, midpoint, false repeated-state window, missing complement at the raw maximum, and terminal offset. Every mutant is rejected because Lean evaluates its mathematical proposition to false, not because of syntax or a missing typeclass. The additive source contains no `axiom`, `sorry`, `admit`, or `native_decide`.

`SOURCE-SHA256SUMS.txt`, `OBJECT-SHA256SUMS.txt`, `PAYLOAD-SHA256SUMS.txt`, and `manifest.json` freeze the exact new source, all predecessor copies, fresh OLEAN objects, scripts, checks, and pins. Independent copied-source replay of this author packet is the next formal gate.
