# Two-parameter zero-rotatability families from alpha paths

Certificate-and-composition proof, 9 October 2026. A separate agent audit checked the mathematical argument and implemented an independent checker. External mathematical review remains pending; no novelty or priority claim is made.

## Statement

Write `S(k^n,1^m)` for the tree with a distinguished center, `n` arms of `k` edges each, and `m` further leaves incident with the center. Superscripts record multiplicities, not powers. For `n=2,m=0` this is a path with a distinguished midpoint; we include this boundary case even if one's definition of spider requires degree at least three.

**Theorem.** For every `k in {3,5,7,9}`, every integer `n>=2`, and every integer `m>=0`, `S(k^n,1^m)` is zero-rotatable. In other words, for each prescribed vertex `v`, it has a bijective labeling with `0,...,nk+m`, assigning `v` zero and inducing every edge difference `1,...,nk+m` exactly once.

In particular this includes `S(9,9,9,1^m)` for every `m>=0`, and extends the seven-edge-arm result to arbitrary numbers of long arms and to no short leaves. The theorem does not cover arbitrary odd `k`, even `k`, or unequal long-arm lengths. There is no requirement that the resulting labeling be an alpha-labeling.

**General partial result.** For every odd `k>=3`, `n>=2`, and `m>=0`, zero can be prescribed at the center, at depths `1,2,k-1,k` on any long arm, or at any short leaf when one exists. Coincident depths are counted only once.

## 1. An explicit center-zero construction

This is a specialization of the standard labeling for rooted symmetric trees (compare Rofa's Theorem 1); a direct verification is supplied here. For any integers `k>=1`, `h>=0`, `m>=0`, label the center of `S(k^h,1^m)` by zero. Index long arms by `i=0,...,h-1` and their depths by `j=1,...,k`. Put

```
b(i,j) = (h-i)k - (j-1)/2      if j is odd,
b(i,j) = ik + j/2              if j is even.
```

Give the short leaves the labels `hk+1,...,hk+m`.

For each block `[ak+1,(a+1)k]`, its first `floor(k/2)` labels come from the even depths of arm `a`. Its last `ceil(k/2)` labels come from the odd depths of arm `h-1-a`. Thus the long arms use exactly `1,...,hk`.

The center edges have differences `(h-i)k`, giving all positive multiples of `k` up to `hk`. The internal differences of arm `i` are

```
|(h-2i)k-s|,    1<=s<=k-1.
```

Writing `a=h-2i`, this is the block `[bk+1,(b+1)k-1]`, where `b=a-1` for `a>0` and `b=-a` for `a<=0`. As `i` ranges over its arms, these `b` values are a permutation of `0,...,h-1`: the positive `a` give `h-1,h-3,...`, and the nonpositive `a` give the remaining parity in increasing order. These blocks and the multiples of `k` partition `1,...,hk`. The short-leaf differences fill `hk+1,...,hk+m`. This proves gracefulness with center zero, including `h=0`, when only a star remains, and `h=m=0`, when just the center remains.

## 2. Alpha-path composition with prescribed extreme labels

The following is the familiar alpha-amalgamation construction, stated with the location of the extreme labels retained. It is not claimed as a new composition method.

Let `H=P_(2k+1)` be the path with positions `0,...,2k` and designated center at position `k`. Suppose `a` is a graceful labeling of `H` with alpha threshold `A`: every edge has one endpoint labeled at most `A` and one above `A`. Require `a(k)=A`.

Let `G=S(k^(n-2),1^m)` with the center-zero labeling `b` from Section 1, and put `Q=(n-2)k+m`. Identify the two centers and define

```
f(v)=b(v)+A                       on G,
f(v)=a(v)                         on H when a(v)<=A,
f(v)=a(v)+Q                       on H when a(v)>A.
```

The two rules agree at the shared center. The `G` labels are `[A,A+Q]`; the low `H` labels are `[0,A]`; and the high `H` labels are `[A+Q+1,2k+Q]`. Their only repeated value is `A` at the identified vertex. Hence the labeling is a bijection onto `[0,nk+m]`.

The `G` differences stay `1,...,Q`. Every `H` edge crosses the alpha threshold, so each of its differences grows by `Q` and these differences become `Q+1,...,Q+2k`. Thus the result is graceful. The vertex with `a=0` stays zero, and the vertex with `a=2k` gets the overall maximum `nk+m`. Complementing every label about `nk+m` makes the latter vertex zero.

This proves the **path reduction**: every depth occurring as the location of `0` or `2k` in such an alpha path is available as a prescribed zero depth in `S(k^n,1^m)`, for every `n>=2,m>=0`. Permuting equal arms puts it on any desired arm. For `Q=0`, the construction is simply the original path.

## 3. A uniform formula for depths one and two

Let `k=2r+1`, `r>=1`, and let `H` have center label `A=2r`. On its left arm put

```
a_L(2j+1)=4r+2-j,    0<=j<=r,
a_L(2j)=j-1,        1<=j<=r.
```

On its right arm put

```
a_R(2j+1)=2r+1+j,    0<=j<=r,
a_R(2j)=2r-j,       1<=j<=r.
```

The low labels are the center `2r`, the left even labels `0,...,r-1`, and the right even labels `r,...,2r-1`. The high labels are the disjoint intervals `[3r+2,4r+2]` on the left and `[2r+1,3r+1]` on the right. Every edge crosses `A=2r`.

The right-arm differences, from the center outward, are `1,2,...,2r+1`. The first left-arm difference is `2r+2`; the rest are `4r+2,4r+1,...,2r+3`. Thus every difference `1,...,4r+2=2k` occurs once. The left arm has `2k` at depth one and `0` at depth two. Section 2 gives the claimed two zero positions for every odd `k>=3` and all `n,m` in the theorem.

## 4. Center, long tips, their neighbors, and short leaves

The center case is Section 1. The following elementary operation supplies the other cases and is the reversible leaf construction discussed by Patterson (Theorem 5.3.6).

If a graceful tree has `q` edges and a specified vertex labeled zero, attach a leaf at that vertex with label `q+1`. Old differences are unchanged and the new edge difference is `q+1`. Complement all labels about `q+1`. The new leaf is now zero and the old zero vertex has the new maximum.

For a selected long arm, start with the center-zero construction on `S(k^(n-1),1^m)`. Apply the operation `k` times, each time attaching at the current zero endpoint. This grows exactly the removed arm and places zero at its tip. Its predecessor has label `nk+m`, so a final complement places zero at depth `k-1`.

For a selected short leaf, when `m>=1`, start with center-zero `S(k^n,1^(m-1))` and apply the operation once. The selected new short leaf is zero. Existing short leaves are interchangeable. The argument works also when any of the starting trees is a path or a single vertex.

Together Sections 1–4 prove the general partial result. This is an all-parameter construction, not an extrapolation from tests.

## 5. Six finite alpha-path certificates

The following paths are listed from left endpoint to right endpoint. Entry `k` (with zero-based indexing) is the designated center and has label `A=k-1`. The last two columns give distances from that center to labels zero and `2k`. All are exact certificates in `certificates.json`.

| k | Path labels, from one endpoint to the other | Zero depth | Maximum depth |
|---:|---|---:|---:|
| 5 | `(9,1,10,0,7,4,5,3,8,2,6)` | 2 | 3 |
| 7 | `(12,3,13,1,14,0,11,6,7,5,8,4,10,2,9)` | 2 | 3 |
| 7 | `(10,1,14,0,12,2,13,6,7,5,8,4,9,3,11)` | 4 | 5 |
| 9 | `(15,3,16,2,17,1,18,0,11,8,9,7,13,4,14,6,10,5,12)` | 2 | 3 |
| 9 | `(16,2,17,1,18,0,13,4,10,8,9,6,14,3,15,5,12,7,11)` | 4 | 5 |
| 9 | `(17,1,18,0,15,4,12,7,9,8,11,5,14,2,16,3,13,6,10)` | 6 | 7 |

Each uses exactly `0,...,2k`, alternates across `A=k-1`, and has these difference sequences:

| k | Zero depth | Consecutive edge differences |
|---:|---:|---|
| 5 | 2 | `(8,9,10,7,3,1,2,5,6,4)` |
| 7 | 2 | `(9,10,12,13,14,11,5,1,2,3,4,6,8,7)` |
| 7 | 4 | `(9,13,14,12,10,11,7,1,2,3,4,5,6,8)` |
| 9 | 2 | `(12,13,14,15,16,17,18,11,3,1,2,6,9,10,8,4,5,7)` |
| 9 | 4 | `(14,15,16,17,18,13,9,6,2,1,3,8,11,12,10,7,5,4)` |
| 9 | 6 | `(16,17,18,15,11,8,5,2,1,3,6,9,12,14,13,10,7,4)` |

These are permutations of `1,...,2k`; their entries can be checked directly. The path reduction therefore makes every indicated depth a valid zero position for all `n>=2,m>=0`.

For `k=3`, Sections 3–4 already cover all depths. For `k=5`, the certificate adds depth 3. For `k=7`, the certificates add depths 3,4,5. For `k=9`, they add depths 3,4,5,6,7. With center and short leaves already covered, every vertex has been covered. This completes the theorem.

The argument does not require claiming that these are exactly the automorphism orbits in every degenerate case. It explicitly covers the distinguished center, every depth on every arm by arm permutations, and every short leaf by leaf permutations.

## 6. A rigorous obstruction to this route for even arm lengths

**Obstruction.** For `k=2r>=2`, there is no graceful labeling of the path `P_(2k+1)` having midpoint label `k` and label `2k` on a neighbor of that midpoint. Thus an alpha-path composition with the midpoint at its alpha index cannot supply a depth-one zero in an even-length equal-arm spider by putting the path maximum there. It cannot put the path zero there either, since the midpoint and its neighbors are on opposite alpha sides.

Proof: write `q=4r`. The proposed midpoint label is `2r`. Its neighbor `q` must also be adjacent to label zero, to realize difference `q`, so the arm begins `(2r,q,0)`. Vertex `q` now has both neighbors. Difference `q-1` forces zero's other neighbor to be `q-1`: the alternative pair `(1,q)` is unavailable. Descending through the largest remaining differences forces an alternating chain

```
2r, 4r, 0, 4r-1, 1, 4r-2, 2, ... , 3r+1, r-1.
```

Here is the induction that rules out competing pairs. Before forcing difference `q-s`, every label outside the still unused middle interval belongs to that chain. All earlier chain vertices except its current endpoint and the midpoint already have full path degree. For even `s=2j`, the only unsaturated low-high pair with difference `q-2j` is `(j,q-j)`; for odd `s=2j+1`, it is `(j,q-j-1)`. The midpoint cannot participate because its distance to any label is at most `2r`, while the differences being forced exceed `2r`. Thus each step must extend the displayed chain until its length reaches `2r=k` edges.

The last vertex `r-1` is now the path endpoint. Every used vertex on that arm except the midpoint is saturated. The still required difference `2r+1` cannot use that arm. All remaining vertices, together with the midpoint, have labels in `[r,3r]`, of width `2r`. Hence they cannot realize difference `2r+1`, a contradiction.

In an alpha-labeling of this even-`k` path with midpoint on the low side, that side contains `k+1` vertices, so bijectivity forces the alpha index to be `k`. The obstruction therefore applies to the stated reduction for every even `k`. It is not an obstruction to zero-rotatability of the spider, or to other graceful constructions. The earlier `k=4` spider certificates already illustrate that distinction.

## Reproduction and evidence limits

Run from this directory with Python 3.10 or later (standard library only):

```sh
python -B verify.py
python -B independent/verify_independent.py
python -B construct.py 9 3 1 5
```

The six exact certificates are included directly; a search program is not needed to check them. See `SOURCE-README.md` for the disclosed packaging changes and `REPRODUCIBILITY.md` for extraction checks.

`verify.py` rebuilds each graph and checks vertex and edge multisets independently of the search. It uses `construct.py` solely to produce labelings and checks the exact requested zero vertex. Its recorded result is 1,440 center-formula checks, 100 odd-formula checks, six finite path certificates, 652 full representative labelings, and 2,352 checks with zero prescribed at an exact vertex. Two deliberately corrupted inputs are rejected. Cases include every vertex for `n=2,3,4,5,8`, `m=0,1,2,5`, and all four stated `k`, plus larger stress examples.

The unbounded claims rest on the formulas, interval proof, and complete depth coverage above. These computations are transcription and implementation checks; they are neither formal proof-assistant verification nor external peer review. The construction and checker were prepared in the same research session. See `literature.md` for the explicitly checked prior results and the still-unresolved priority question.

The next precise mathematical question is whether the alpha-path condition can be met for all odd `k>=3` and each even depth `d` with `2<=d<=k-3`, with zero at `d` and maximum at `d+1`. Together with Sections 1–4, an affirmative general construction would prove zero-rotatability of `S(k^n,1^m)` for every odd `k`, `n>=2`, `m>=0`. No such general construction is proved here.
