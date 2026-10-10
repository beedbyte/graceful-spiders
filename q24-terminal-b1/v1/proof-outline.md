# Proof outline

Indices start at zero. A source word of length `2k+1` has high offsets `0..k` at even indices and low offsets `0..k−1` at odd indices. Adjacent offset sums are `0..2k−1` once each. Decode `H_h` as `2k−h` and `L_l` as `l`. This gives a graceful alpha path with cut `k−1`.

The old P20/q24 family has odd `k`, physical midpoint `X[k]=k−1`, endpoint `H12`, and a window `H1,L0,H0,L2` with the `L0` at odd index `z`, `z+2<k`. After `s` ordinary steps, `k=23+24s` and `z=3+2s`.

The certificate has block lengths `|B|=1`, `|D|=23`, `|A|=24`. B is low, D alternates high to high, and A alternates low to high. Its high and low inventories each contain `1..24` once. The three chains `H25–B–H0`, `L0–D–L26`, `H36–A` have sums `1..50` once; `A` ends at `H12`. The portable checker verifies these exact conditions and the Lean source proves them by kernel computation.

For any source satisfying the contract, form

```
Y = (X[:z]+24) ++ B ++ [H0,L0] ++ D ++ (X[z+2:]+24) ++ A.
K = k+24.
```

The removed old sums are `1,0,2`. Retained edge sums increase by 48, filling `51..2K−1`; the new chains fill `1..50`, and the reversed zero pair supplies zero. Positive old offsets and the fresh inventories fill both sides without collision. There are 24 additional positions before the old midpoint and 24 after it, so the physical midpoint becomes `K`, labeled `K−1`. The maximum is at index `z+1` and zero at `z+2`. The old state is an input contract only: the flipped output is not iterated.

Set `s=t−1`. The resulting source has `K=23+24t`, maximum at depth `21+22t` and zero at depth `20+22t` from its midpoint.

For any selected arm `a`, choose a different arm `b`. Let `h=n−2`, `Q=hK+m`, and `N=nK+m`. Label the residual hub zero, residual arm of rank `i` at depth `d` by

```
K(h−i)−(d−1)/2,  d odd;
Ki+d/2,         d even;
```

and short leaf `j` by `hK+j+1` (`0≤j<m`). These labels and edge differences cover `0..Q` and `1..Q`. For internal arm edges the blocks are indexed by `h−2i−1` if `h−2i>0`, and `2i−h` otherwise; these permute `0..h−1`. This includes the singleton residual when `n=2,m=0`.

Shift the residual by `K−1`; keep the source low labels and increase its high labels by Q. Identify the source midpoint with the residual hub; assign source indices `K−d` to arm a and `K+d` to b. Label bands meet only at the hub and edge-weight bands are `1..Q` and `Q+1..N`. All actual named vertices, including the original leaves, are present. The low zero gives the lower depth directly. Complementing every label by `N−label` gives the upper depth at the former maximum.

The formal theorem proves precisely these two depths. Combining the result with the separately established D8/q24 prefix gives the mathematical corollary `1≤d≤21+22t=(11K−1)/12` for `t≥5`. That prefix union is not an additional Lean theorem in this source package, and the limiting ratio remains 11/12. The exact wider literature priority remains unresolved.
