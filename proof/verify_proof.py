"""Independent exact checks for the base certificates and insertion invariant."""

import json
from pathlib import Path


def edges(m):
    out = []
    for i in range(3):
        out += [("center", f"a{i}1"), (f"a{i}1", f"a{i}2"), (f"a{i}2", f"a{i}3")]
    out += [("center", f"p{i}") for i in range(m)]
    return out


def check(m, role, f, t):
    q = m + 9
    names = {"center"} | {f"a{i}{j}" for i in range(3) for j in (1, 2, 3)} | {f"p{i}" for i in range(m)}
    assert set(f) == names
    assert set(f.values()) == set(range(q + 1))
    zero = next(v for v, x in f.items() if x == 0)
    assert (zero == "center" if role == "center" else
            zero in {f"p{i}" for i in range(m)} if role == "leaf" else
            zero in {f"a{i}{role[-1]}" for i in range(3)})
    es = edges(m)
    assert sorted(abs(f[u] - f[v]) for u, v in es) == list(range(1, q + 1))
    d = f["center"] - t if f["center"] > t else t + 1 - f["center"]
    stationary = sorted(abs(f[u] - f[v]) for u, v in es if (f[u] > t) == (f[v] > t))
    rising = sorted(abs(f[u] - f[v]) for u, v in es if (f[u] > t) != (f[v] > t))
    assert stationary == list(range(1, d)), (role, m, stationary, d)
    assert rising == list(range(d, q + 1)), (role, m, rising, d)
    return d


def main():
    records = json.loads(Path(__file__).with_name("bases.json").read_text(encoding="utf-8"))
    assert set(records) == {"center", "arm1", "arm2", "arm3", "leaf"}
    for role, record in records.items():
        t = record["threshold"]
        f = record["labels"]
        first_d = check(1, role, f, t)
        for m in range(1, 101):
            check(m, role, f, t)
            f = {name: x + (x > t) for name, x in f.items()}
            f[f"p{m}"] = t + 1
        print(f"{role}: base d={first_d}; exact invariant verified for m=1..100")


if __name__ == "__main__":
    main()
