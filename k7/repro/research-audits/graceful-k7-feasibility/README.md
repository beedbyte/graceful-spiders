# Internal feasibility audit: `S(7,7,7,1^m)`

**Updated status (2026-10-08): all nine orbits now proved for every m>=1.** The subsequent [internal continuation](continuation.md) supplies four new seeds, three complements, an independent checker, a conditional odd-arm tip reduction, and a cut obstruction explaining one unsuccessful old parameter pair. Run `python research-audits/graceful-k7-feasibility/verify-continuation.py` for all nine orbits. Scientific novelty and publication priority remain unresolved.

The remainder of this README records the earlier bounded feasibility stage, when seven arm-depth orbits were UNKNOWN. Its original two-row checker and search records are preserved as historical evidence; their UNKNOWN wording is superseded by the continuation above.

For `m=1`, there are `q=22` edges and nine vertex orbits: center, arm depths 1–7, and center leaf. The file [`bases.json`](bases.json) contains an exact leaf-zero certificate. Its complement `x -> 22-x` gives center-zero. The independent, solver-free [`verify.py`](verify.py) checks the vertex bijection, all 22 individual edge differences, the zero-label orbit, and the threshold partition; it then checks the insertion recurrence for `m=1..100` as a diagnostic. Run from the repository root:

```powershell
python research-audits/graceful-k7-feasibility/verify.py
```

Expected output:

```text
leaf: PASS; t=0; d=22; m=1..100
center: PASS; t=21; d=22; m=1..100
2 of 9 zero-label orbits covered; remaining 7 UNKNOWN.
```

## Certificates and exact threshold condition

The leaf-zero row has center `22`, center leaf `0`, and arms

```text
[1,21,2,20,3,19,4]
[8,5,12,11,16,10,14]
[9,17,7,18,6,15,13]
```

Its threshold is `t=0`. All labels are `0..22` once. The same-side edge differences (both endpoints at most `t` or both above `t`) are `1..21`; the crossing edge difference is `22`. Complementing all labels produces center zero, threshold `t=21`, the same partition, and center leaf `22`. Thus the common *form* of the insertion invariant holds for two orbits, with a fixed threshold for each certificate; the thresholds need not equal each other.

For any row with center label `c`, threshold `0<=t<=q`, put `d=c-t` when `c>t`, and `d=t+1-c` otherwise. The insertion condition is that same-side differences are exactly `1..d-1` and crossing differences exactly `d..q`. Insert a new center leaf with label `t+1`, and increase every old label above `t` by one. This preserves the bijection and zero label. Old same-side differences stay fixed; old crossing differences increase by one. If `c<=t`, the new edge crosses the threshold with difference `d`, so the crossing interval becomes `d..q+1`. If `c>t`, the new edge is same-side with difference `d`, and the new center label makes the next value of `d` equal `d+1`; the intervals become `1..d` and `d+1..q+1`. This proves indefinite insertion **for either supplied orbit**. It does not prove the seven missing arm orbits.

## Reproducible bounded search

[`leaf-template.js`](leaf-template.js) fixes center `22`, leaf `0`, and arm 0 to `[1,21,2,20,3,19,4]`, then searches the remaining two arms by distinct labels and edge differences. It found the row above at node `180975`:

```powershell
node research-audits/graceful-k7-feasibility/leaf-template.js 100000000
```

[`search.js`](search.js) explores threshold-constrained DFS trees for each arm-zero orbit, with label `22` on an adjacent arm vertex. It checks candidate rows internally, but the Python checker above is the independent authority. Node budgets count DFS entries. A per-pair budget truncates each `(threshold, center label)` pair, so even a run that visits all pairs is not an exhaustive nonexistence proof. Reproduce the broad runs:

```powershell
$roles=@('arm1','arm3','arm5','arm7'); foreach($role in $roles) { node research-audits/graceful-k7-feasibility/search.js $role 100000000 20000 }
```

These yielded UNKNOWN with `(nodes, pairs)` respectively `(6290473,341)`, `(7848915,462)`, `(8003109,462)`, `(8052640,462)`. The selected deeper runs below also yielded UNKNOWN, each after `50000001` DFS entries in one parameter pair:

```powershell
node research-audits/graceful-k7-feasibility/search.js arm1 50000000 50000000 2 20
node research-audits/graceful-k7-feasibility/search.js arm3 50000000 50000000 1 20
node research-audits/graceful-k7-feasibility/search.js arm5 50000000 50000000 2 19
node research-audits/graceful-k7-feasibility/search.js arm7 50000000 50000000 2 19
```

The adjacent-maximum restriction lets a successful arm-1, arm-3, or arm-5 row cover depths 2, 4, or 6 by complement when the maximum sits at that depth. The arm-7 attempt places the maximum at depth 6. This is a search design, not a proof that all possible threshold rows have that arrangement. No arm-depth certificate was found in these bounds, so all seven depths remain UNKNOWN. Search failure says nothing about 0-rotatability itself.
