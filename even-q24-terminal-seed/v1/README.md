# A conditional zero window from terminal-12 even seeds

**Beedbyte · source package v1**

Jordi Gartner publishes this work through Beedbyte. English is the source text. The German and simplified Chinese versions are translation drafts without recorded human language review.

## Result

Assume an even terminal-12 seed `(K0,z0,c)` satisfying the finite conditions in the formal statement: `K0≥26` is even; `z0≥3` is odd with `z0+2<K0`; the even-index tags are a permutation of `0,…,K0`, the odd-index tags a permutation of `0,…,K0−1`, the adjacent sums a permutation of `0,…,2K0−1`, the midpoint tag is `K0`, the local tags are `[1,0,0,2]`, and the last tag is 12. For every `t≥0`, put `K=K0+24t`. For every integer depth

`K0−z0−1+20t ≤ d ≤ K0−z0+22t`,

there is a conventional graceful labeling with zero at the selected vertex on either one of the two named new K-edge arms. Each target has its own labeling. This holds after identifying the path midpoint with a supplied root `r` of any finite graph `H` carrying a conventional graceful labeling `g` with `g(r)=0`. The theorem does not require `H` to be a tree, connected or vertex-onto. It says nothing about old vertices of `H`, and does not assert simultaneous zeros.

## Literal bases and the D8 seam

The included literal seed data records `(K0,z0)=(26,5),(28,9),(30,3)`. Their respective windows are `[20+20t,21+22t]`, `[18+20t,19+22t]`, and `[26+20t,27+22t]`. The formal source proves the K28 and K30 seed validations and window specializations; K26 is the previously frozen literal seed record and is not presented as a new theorem in this source closure. For K30 only, the exact D8 seam begins at `t=4`; the two guarantees then join to `2≤d≤27+22t` on either new arm for all `t≥4`. No seam is asserted for the K26 or K28 cases in this package.

The result is conditional on a qualifying seed. It does not prove such a seed exists for every even `K0`, does not cover every depth, every even arm length, old vertices or a simultaneous two-zero labeling. Historical priority is not claimed.

## Proof, prior operations and verification

The seed family reuses the established B2/B4 q24 insertion gadgets and the existing midpoint-alpha path/rooted-graph graft. The generic alpha amalgamation is prior work: Huang–Kotzig–Rosa’s construction is stated explicitly in [Panpa, Imnang and Wasuanankul (2025), Theorem 2.5](https://onlinelibrary.wiley.com/doi/full/10.1155/jama/5826777) and [Shan–Zhong (2026), Lemma 1](https://arxiv.org/html/2605.14295v2). See also [Barrientos (2022), *On the generation of alpha graphs*](https://www.jacodesmath.com/index.php/jacodesmath/article/view/194) and [Barrientos–Minion (2019), §2.2](https://digitalcommons.georgiasouthern.edu/tag/vol6/iss1/4/). The package does not claim a new generic graft operation or historical priority.

The conditional family, K28/K30 literals and K30 seam are proved in Lean 4.34.0. A separate internal copied-source replay compiled all 84 modules, checked nine principal axiom closures against the standard Lean axioms, and rejected ten false semantic controls. These are internal project checks, not external review or peer review. The trust boundary includes Lean’s kernel, compiler and standard library. Run `python verify_package.py` for an integrity check. A fresh Lean build is available with `python -B build.py --lean /path/to/lean --output /new/outside/package/objects`; it requires the pinned Lean 4.34.0 executable (SHA256 `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`) and compiles only the packaged source into a new output directory. Exact reports and seed data are in `evidence/`; payload hashes are in `PAYLOAD-SHA256.json`.

AI tools assisted the documented Lean proof development and checking scripts, and drafted the German and Chinese translations.

Version 1 adds the conditional terminal-12 seed window, the K28 and K30 specializations, and the K30 D8 seam result.
