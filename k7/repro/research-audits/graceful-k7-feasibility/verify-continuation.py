"""Independent, exact integer checker. Python standard library; no search imports.

The unbounded conclusion uses the insertion proof in continuation.md. Tests of
m=1..100 are diagnostics. An additional affine check verifies the base-edge
formulas for every integer m>=1, without sampling m.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


def edges(m):
    return [("c" if j == 1 else f"a{i}:{j-1}", f"a{i}:{j}")
            for i in range(3) for j in range(1, 8)] + [("c", f"p{j}") for j in range(m)]


def unpack(row):
    require(len(row["arms"]) == 3 and all(len(a) == 7 for a in row["arms"]), "arm lengths")
    return {"c": row["center"], "p0": row["p0"],
            **{f"a{i}:{j}": x for i, a in enumerate(row["arms"]) for j, x in enumerate(a, 1)}}


def check(role, labels, t, m):
    q = 21 + m
    es = edges(m)
    require(set(labels) == {v for edge in es for v in edge}, f"{role}: vertices")
    require(sorted(labels.values()) == list(range(q+1)), f"{role}: label bijection")
    target = {"center": "c", "leaf": "p0"}.get(role, f"a0:{role[3:]}")
    require(labels[target] == 0, f"{role}: zero")
    require(0 <= t <= q, f"{role}: threshold")
    c = labels["c"]
    d = c-t if c > t else t+1-c
    same, cross = [], []
    for u, v in es:
        x, y = labels[u], labels[v]
        (same if (x > t) == (y > t) else cross).append(abs(x-y))
    require(sorted(same+cross) == list(range(1, q+1)), f"{role}: edge bijection")
    require(sorted(same) == list(range(1, d)), f"{role}: same interval")
    require(sorted(cross) == list(range(d, q+1)), f"{role}: cross interval")
    return d


def affine_base_edges(labels, t):
    # Store each old vertex as a*m+b. High labels x become m+(x-1).
    affine = {v: (1, x-1) if x > t else (0, x) for v, x in labels.items()}
    same, cross = [], []
    for u, v in edges(1):
        lo, hi = sorted((u, v), key=labels.get)
        a = affine[hi][0] - affine[lo][0]
        b = affine[hi][1] - affine[lo][1]
        require(a >= 0 and a+b > 0, "absolute-value sign valid for all m>=1")
        (cross if a else same).append((a, b))
    c = labels["c"]
    d = c-t if c > t else t+1-c
    require(sorted(same) == [(0, x) for x in range(1, d)], "constant edge formulas")
    require(sorted(cross) == [(1, x-1) for x in range(d, 23)], "growing edge formulas")
    # p_j=t+m-j, 1<=j<=m-1. Difference from center is d+j-1
    # for high center, d+m-j-1 for low center; either gives d..d+m-2.
    require((c-t-1 if c > t else t-c) == d-1, "inserted leaf formula")


def cut_identity(labels, t):
    if labels["c"] <= t:
        return
    low = {v for v, x in labels.items() if x <= t}
    leaves = {"p0", "a0:7", "a1:7", "a2:7"}
    ell = len(low & leaves)
    internal = sum(u in low and v in low for u, v in edges(1))
    require(22-labels["c"] == t+1-ell-2*internal, "cut identity")


def main():
    old = json.loads((ROOT / "bases.json").read_text(encoding="utf-8"))
    new = json.loads((ROOT / "continuation-bases.json").read_text(encoding="utf-8"))
    rows = {}
    for data in (old, new):
        require(data["q"] == 22 and data["base_m"] == 1, "base size")
        for role, row in data["seeds"].items():
            rows[role] = (unpack(row), row["threshold"])
        for role, source in data["complements"].items():
            labels, t = rows[source]
            rows[role] = ({v: 22-x for v, x in labels.items()}, 21-t)
    require(set(rows) == {"center", "leaf", *(f"arm{j}" for j in range(1, 8))}, "nine orbits")
    for role, (base, t) in rows.items():
        d = check(role, base, t, 1)
        affine_base_edges(base, t)
        cut_identity(base, t)
        for m in range(2, 101):
            labels = {v: x+(m-1 if x > t else 0) for v, x in base.items()}
            labels.update({f"p{j}": t+m-j for j in range(1, m)})
            check(role, labels, t, m)
        print(f"{role}: PASS; t={t}; base d={d}; affine formulas; m=1..100")
    r = new["tip_reduction_seed"]
    vals = [r["center"], r["leaf"], *r["arms"][0], *r["arms"][1]]
    diffs = [abs(r["center"]-r["leaf"])]
    for arm in r["arms"]:
        diffs.extend(abs(x-y) for x, y in zip([r["center"]]+arm, arm))
    require(sorted(vals) == list(range(16)) and sorted(diffs) == list(range(1, 16)), "reduced witness")
    a7 = new["seeds"]["arm7"]
    require(a7["arms"][1:] == [[x+4 for x in a] for a in r["arms"]], "lift arms")
    require(a7["center"] == r["center"]+4 and a7["p0"] == r["leaf"]+4, "lift center/leaf")
    # A low zero-labeled tip has degree1; the other two low vertices have
    # degree at most2. Thus a t=2 cut has at most5 edges, but c=19 requires6.
    require(1+2+2 < 22-(19-2)+1, "arm7 t2 c19 obstruction")
    print("9 of 9 zero-label orbits verified; reduced tip witness PASS.")
    print("Cut identity PASS; arm7 with t=2, c=19 is impossible for this insertion invariant.")


if __name__ == "__main__":
    main()
