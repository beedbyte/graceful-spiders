# One even-state q24 seed criterion and three residue classes

10 October 2026. Private additive mathematical author packet. **GO for the conditional symbolic criterion and the exact K30 literal below; separate independent QA of this new packet remains open.** The K26 and K28 inputs have independently frozen mathematical GO. No public change, world-priority claim, or all-even-K extrapolation.

## Source inventory and what is stronger

The independently audited K26 family report is SHA-256 `40862d2d3f7dad6bc75724f8d7715d8e5ec78ed7e76925a7913146370f40aad5`; its base is `(K0,z0)=(26,5)` and its interval is `[20+20t,21+22t]`. The independently audited K28 report is SHA-256 `ab7ecbbd0de8d5f3a10df2da0ac017439c2c5916a3d51c1c5707c537f9dc3f92`; its base `(28,9)` gives `[18+20t,19+22t]`. Both retain the previously frozen q24 B2/B4 *finite insertion gadgets*; neither instantiates the old odd-k `State` theorem head. The old D8 theorem supplies `2..D8(K)` at each K, while both new upper endpoints lie strictly above its stated bound. Fixed-K actual-spider shell/endpoint results may cover the same vertices, but do not themselves supply this even midpoint-alpha path interface over an arbitrary root-zero residual graph. These are scoped source-contract comparisons; global historical priority and exhaustive closure of all older constructions remain UNKNOWN.

## A single sufficient seed condition

Let `K0≥26` be even. A **terminal-12 even seed** consists of an odd integer `z0≥3` with `z0+2<K0` and a list `c[0..2K0]` such that:

1. Even-index tags are a permutation of `0..K0`; odd-index tags are a permutation of `0..K0−1`.
2. Its `2K0` adjacent sums are a permutation of `0..2K0−1`.
3. `c[K0]=K0`, `c[z0−1..z0+2]=[1,0,0,2]`, and `c[2K0]=12`.

These are literal finite conditions on **one** word. The inventories force `c[0]+c[2K0]=K0` by summing all edge sums two ways, hence `c[0]=K0−12`. This immediately excludes the same terminal-12 interface at K0=24: its first and last high-side entries would both equal12. It does not exclude other interfaces or graphs at K24.

Decode even positions by `w_i=c_i` and odd positions by `w_i=2K0−c_i`. Side completeness gives the labels `0..2K0`; every adjacent difference is `2K0−(c_i+c_{i+1})`, giving weights `1..2K0`. Every edge crosses the cut K0, the actual midpoint index K0 has label K0, and the local zeros decode to maximum `2K0` at index z0 and zero at index z0+1. Thus this one finite condition supplies the exact midpoint-alpha path needed by the previously independently replayed conventional root-zero graft. Reversal exchanges the two named new arms and whole-graph complement converts a maximum target into zero, with a separate labeling for each target. Residual H may be cyclic, disconnected or nononto labeled; it only needs a supplied conventional graceful labeling with root zero. Nothing is asserted for old H vertices.

## Universal B2/B4 consequence

For a valid even seed, remove its adjacent zero tags, shift all retained positive tags by24, and insert either frozen B2 or B4 gadget with `[0,0]` between its B and D segments, followed by its A segment. Both gadgets have `|B|+|D|=24`, `|A|=24`; the two local tag-parity inventories give the fresh `0..24` bands, and their three join/internal chains give sums `1..50`. The surviving old sums `3..2K−1` shift by48 to `51..2K+47`, while the new zero edge supplies0. The retained midpoint moves 24 indices and its tag gains24; terminal12 and the four-tag local window remain valid. These side/sum/index calculations are independent of K being odd and are fully stated in the frozen K26/K28 mathematical audits; `check.py` replays both literal gadget inventories here.

After t steps, let j be the number of B4 steps. The order is arbitrary and

`K=K0+24t`, `z=z0+2t+2j`, `d∈{K0−z0−1+22t−2j, K0−z0+22t−2j}`.

As j ranges0..t, adjacent pairs cover the entire closed interval

**`[K0−z0−1+20t, K0−z0+22t]`**

on either new arm, with separate graceful zero labelings over every supplied root-zero H. This is a conditional theorem for *any* seed satisfying the finite criterion; it is not an assertion that such a seed exists for every even K0.

## Exact D8 gap-to-seam formula

For `K=K0+24t≥126`, put `a=(z0−17)/2`, `c=K0/2−63` and `u=floor((12t+c)/11)`. The accepted D8 large branch simplifies to `D8(K)=K−19−2u`. The new upper depth minus D8 and the seam margin are exactly

`(K0−z0+22t)−D8(K)=2(u−t−a+1)`,

`D8(K)+1−(K0−z0−1+20t)=2(2t+a−u)`.

Thus a strict gain and a contiguous join hold exactly when `t+a≤u≤2t+a`. In integer arithmetic, it is sufficient and necessary within this large branch that

`t≥11a−c` and `10t≥c−11a−10`.

Together with `K0+24t≥126`, these give an explicit finite threshold for **every valid seed**. Since `u=t+floor((t+c)/11)`, the gain above D8 grows without bound and the seam margin eventually becomes positive. This proves a conditional unbounded prefix improvement for every seed, without enumerating more K0 or inferring a K0→K0+2 seed recurrence.

For the three proved seeds the exact arithmetic is:

| Base `(K0,z0)` | New interval | First t with large-branch seam and strict gain | Further finite seam |
|---|---|---:|---|
| `(26,5)` | `[20+20t,21+22t]` | 5 | none claimed |
| `(28,9)` | `[18+20t,19+22t]` | 5 | t=2 also joins D8 |
| `(30,3)` | `[26+20t,27+22t]` | 4 | none claimed |

The first two rows were already independently audited. In particular the new third row yields prefix `2..27+22t` for every K=`30+24t`, t≥4. At smaller t, the upper new depth still exceeds D8 but the two listed intervals may have gaps.

## One predeclared additional test: K30

The criterion identified K0=30 with `z0∈{3,5,7,9}` as a useful single bounded target: any of these values would meet the D8 seam from the first large branch t4. Before the run, `search_k30.py` fixed that **one combined CP-SAT model**, a 90-second cap and all side/sum/midpoint/terminal/window constraints. The sole run returned z0=3 in 3.95 solver seconds. No other K or follow-up solver model was run. The solver status is discovery provenance, not proof.

The exact independently checked 61-tag word is

```
[18,4,1,0,0,2,2,1,8,15,15,16,21,21,22,22,23,23,24,24,25,25,26,26,27,27,28,28,29,29,30,11,14,14,13,13,11,10,10,9,9,8,7,7,6,6,5,5,3,3,4,12,20,20,19,19,17,18,16,17,12].
```

Its high tags sort to `0..30`, low tags to `0..29`, and its **60 ordered adjacent sums** are

```
[22,5,1,0,2,4,3,9,23,30,31,37,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,41,25,28,27,26,24,21,20,19,18,17,15,14,13,12,11,10,8,6,7,16,32,40,39,38,36,35,34,33,29].
```

They sort to `0..59`. Its midpoint tag is `c[30]=30`, terminal `c[60]=12`, first tag18, and local window `c[2..5]=[1,0,0,2]`. The decoded path is a complete alpha `P61`, with zero/max at indices4/3 and hence depths26/27. These are literal checks, independent of the solver's claim. Earlier fixed-K30 center-one shells and the all-even actual-spider theorem already cover the *spider vertices*; the present result adds a distinct even midpoint-alpha source and arbitrary supplied rooted-H interface relative to inspected project sources.

## Independent executable controls and limits

`check.py` pins both independently audited K26/K28 reports and the exact q24 gadget, D8 and rooted-graft sources. It reads three literal seeds from `seeds.json`, checks every side label, sum, decoded label, edge difference, midpoint, cut and extreme, then checks both gadget inventories, all 45 mixed words through t3, exact position formulas and **30,204 actual nononto triangle graft edges** with both physical orientations and both extreme choices. Seven hostile mutations reject a duplicate tag, wrong zero index, shifted local window, wrong midpoint, wrong terminal, wrong B2/B4 position, and wrong selected graph vertex. Explicit guards make `python -B` and `python -B -O` produce byte-identical results. It checks the D8 formulas through t499 as a falsification aid; the integer identities above prove all t.

The result is conditional beyond the three supplied K0 values. It does **not** prove a K0→K0+2 promotion, all residue classes, or a stronger prefix for every even K. The K30 literal and this combined criterion await separate independent mathematical QA; a Lean theorem is not claimed. Historical priority is unknown.
