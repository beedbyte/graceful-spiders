"""Standalone exact audit of the six S(4,4,4,1) threshold certificates."""

import json
from pathlib import Path


def audit(m, role, labels, threshold):
    q = m + 12
    vertices = {"center"} | {f"a{i}{j}" for i in range(3) for j in range(1, 5)} | {f"p{i}" for i in range(m)}
    assert set(labels) == vertices
    assert sorted(labels.values()) == list(range(q + 1))
    target = ("center" if role == "center" else "p0" if role == "leaf" else f"a0{role[-1]}")
    assert labels[target] == 0

    pairs = []
    for i in range(3):
        path = ["center"] + [f"a{i}{j}" for j in range(1, 5)]
        pairs.extend(zip(path, path[1:]))
    pairs.extend(("center", f"p{i}") for i in range(m))
    diffs = [abs(labels[u] - labels[v]) for u, v in pairs]
    assert sorted(diffs) == list(range(1, q + 1))

    c = labels["center"]
    d = c - threshold if c > threshold else threshold + 1 - c
    classes = {False: [], True: []}
    for u, v in pairs:
        crosses = (labels[u] <= threshold) != (labels[v] <= threshold)
        classes[crosses].append(abs(labels[u] - labels[v]))
    assert sorted(classes[False]) == list(range(1, d))
    assert sorted(classes[True]) == list(range(d, q + 1))
    return d


def main():
    records = json.loads(Path(__file__).with_name("k4_bases.json").read_text(encoding="utf-8"))
    assert set(records) == {"center", "arm1", "arm2", "arm3", "arm4", "leaf"}
    for role, data in records.items():
        t = data["threshold"]
        f = data["labels"]
        d = audit(1, role, f, t)
        for m in range(1, 101):
            audit(m, role, f, t)
            f = {v: x + (x > t) for v, x in f.items()}
            f[f"p{m}"] = t + 1
        print(f"{role}: base d={d}, exact certificates/invariant pass m=1..100")


if __name__ == "__main__":
    main()
