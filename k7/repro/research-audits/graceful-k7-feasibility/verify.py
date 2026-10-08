"""Exact, solver-free verification of the supplied K7 threshold certificates."""
import json
from pathlib import Path

DATA = json.loads(Path(__file__).with_name("bases.json").read_text(encoding="utf-8"))
K = 7


def graph(m):
    vertices = {"center", *(f"a{i}{j}" for i in range(3) for j in range(1, K + 1)),
                *(f"p{j}" for j in range(m))}
    edges = []
    for i in range(3):
        prior = "center"
        for j in range(1, K + 1):
            here = f"a{i}{j}"
            edges.append((prior, here))
            prior = here
    edges += [("center", f"p{j}") for j in range(m)]
    return vertices, edges


def check(role, m, labels, t):
    q = 3 * K + m
    vertices, edges = graph(m)
    assert len(edges) == q
    assert set(labels) == vertices, (role, m, "vertices")
    assert sorted(labels.values()) == list(range(q + 1)), (role, m, "bijection")
    zero = {"center": "center", "leaf": "p0"}.get(role, f"a0{role[3:]}")
    assert labels[zero] == 0, (role, m, "zero orbit")
    assert 0 <= t <= q
    c = labels["center"]
    d = c - t if c > t else t + 1 - c
    same, crossing, all_diffs = [], [], []
    for u, v in edges:
        x, y = labels[u], labels[v]
        diff = abs(x-y)
        all_diffs.append(diff)
        (same if (x > t) == (y > t) else crossing).append(diff)
    assert sorted(all_diffs) == list(range(1, q + 1)), (role, m, "graceful")
    assert sorted(same) == list(range(1, d)), (role, m, "same-side interval")
    assert sorted(crossing) == list(range(d, q + 1)), (role, m, "crossing interval")
    return d


def unpack(row):
    assert len(row["arms"]) == 3 and all(len(arm) == K for arm in row["arms"])
    labels = {"center": row["center"], "p0": row["p0"]}
    labels.update({f"a{i}{j}": x for i, arm in enumerate(row["arms"])
                   for j, x in enumerate(arm, 1)})
    return labels, row["threshold"]


def main():
    assert DATA["family"] == "S(7,7,7,1^m)" and DATA["base_m"] == 1 and DATA["q"] == 22
    rows = {role: unpack(row) for role, row in DATA["seeds"].items()}
    for target, source in DATA["complements"].items():
        labels, t = rows[source]
        rows[target] = ({v: 22-x for v, x in labels.items()}, 21-t)
    assert set(rows) == {"center", "leaf"}
    for role, (base, t) in rows.items():
        d = check(role, 1, base, t)
        labels = base
        for m in range(2, 101):
            labels = {v: x + int(x > t) for v, x in labels.items()}
            labels[f"p{m-1}"] = t + 1
            check(role, m, labels, t)
        print(f"{role}: PASS; t={t}; d={d}; m=1..100")
    print("2 of 9 zero-label orbits covered; remaining 7 UNKNOWN.")


if __name__ == "__main__":
    main()
