# Symbolic inventory and actual graph transfer

Version q48-two-flip-v1. All arrays, including the initial47-entry source and stationary q24 gadget, are in `data.json`; the two complete constituents are `first` and `second`. The mathematical checker derives the q48 macro, and its literal arrays are also present in `source/Q48Graft.lean`.

## Source contract and one terminal insertion

For odd k, a source word X has2k+1 entries. Even positions carry H offsets0..k once; odd positions carry L offsets0..k-1 once. Adjacent offset sums are0..2k-1 once. The physical midpoint index k has low offset k-1. Decode H_h as2k-h and L_l as l; then labels are0..2k and differences1..2k, crossing alpha cut k-1.

The old source has terminal H12 and window H1,L0,H0,L2 at indices z-1..z+2, with z odd and z+2<k. For the initial source k=23,z=3. Each old stationary q24 step increases k by24 and z by2 while retaining this contract.

The two terminal flips have singleton B1=[12] on side L and B2star=[13] on side H. Their D and A block lengths are23 and24. Each phase's fresh high and low sides each contain1..24. In phase1 the three chains

    H25 — B1 — H0;  L0 — D1 — L26;  H36 — A1

partition sums1..50. The new window is L12,H0,L0,H1. In phase2 the chains

    L36 — B2star — L0;  H0 — D2 — H25;  H36 — A2

partition sums1..48 together with49 and60. This is not the first phase's contiguous inventory. Phase2 restores the zero tag order, giving H13,L0,H0,L1 and terminal H12.

Write `+c` for entrywise addition, and `++` for concatenation. The literal composite is

```text
B48=(B1+24)++B2star=[36,13]
D48=D2++(D1+24)
A48=(A1+24)++A2
Y=(X[:z]+48)++B48++[L0,H0]++D48++(X[z+2:]+48)++A48.
```

The three blocks have lengths2,46,48, each alternating L..H. On each side their inventory is1..48. Their complete chains H49-B48-L0, H0-D48-L50, H60-A48 have sums1..98 once. Algebraically, retained phase1 sums after the second shift occupy50..59 and61..98: its zero-boundary sums12 and1 are removed. Phase2 supplies1..49 and60. Their union is1..98.

The untouched original edges, whose sums were3..2k-1, now have sums99..2(k+48)-1. The new zero-zero edge contributes0. Thus every sum0..2(k+48)-1 occurs once. Fresh offsets1..48, shifted old positive offsets and retained zeros give the complete new side inventories. Exactly48 positions are inserted before the old midpoint and48 after it, so the new midpoint is k+48 with low label k+47. The final zero indices are z+2 and z+3.

For t>=2 set u=t-2. The old source has k=23+24u,z=3+2u. The terminal result has K=23+24t, L0 index2t+1 and H0 index2t+2. Their midpoint distances are22+22t and21+22t. At t=2 this gives K=71, depths66 and65; at t=3, K=95, depths88 and87. The proof is symbolic for every t>=2. The output cannot be fed back into the unchanged old State because its neighbors are13 and1, rather than1 and2.

## Residual transfer to S(K^n,1^m)

Choose the requested arm and a distinct partner, possible for n>=2. Let h=n-2, Q=hK+m, N=nK+m. Keep the actual remaining h arms and all m original leaves. Give the residual hub label0. Number its arms i=0..h-1 and use physical depth d:

    g(i,d)=K(h-i)-(d-1)/2          when d is odd;
    g(i,d)=Ki+d/2                 when d is even;
    g(leaf,j)=hK+j+1              for0<=j<m.

For odd K=2r+1, even-position labels on arm i and odd-position labels on arm h-1-i fill the disjoint intervals Ki+1..Ki+r and Ki+r+1..K(i+1). Hub edges give the multiples of K. Internal edges on arm i have weights |K(h-2i)-v|,1<=v<K; their nonmultiple block indices are h-2i-1 when h-2i>0 and2i-h otherwise. These indices partition0..h-1. Leaves supply labels and weights hK+1..Q. Hence the residual is root-zero graceful, including h=m=0 (one hub) and h=0,m=1 (one original leaf).

Shift residual labels by K-1 and raise only the decoded source high labels by Q. Identify the source midpoint with the actual hub, and place indices K-d on the selected arm and K+d on the partner. The label bands are[0,K-1], [K-1,Q+K-1], [Q+K,Q+2K], meeting only at the identified hub. Edge weights partition1..Q and Q+1..N. The source low zero gives depth22+22t. The source high extreme becomes N; complementing every actual label gives zero at21+22t. Each selected target uses a separate labeling. No original leaves are removed, and the selected arm is arbitrary.

The Lean theorem proves the direct macro and this graph consequence. The literal identity between two flips and the macro is also checked by the mathematical implementation; that syntactic two-stage identity is not separately claimed as a Lean theorem. REFERENCES.md credits the cited older path-permutation operations only. The graph transfer just proved here is not historically attributed to those path passages, and no novelty claim is made for it.
