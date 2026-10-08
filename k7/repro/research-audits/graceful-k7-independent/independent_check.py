"""Independent certificate audit: no imports or execution of the supplied checkers.

Vertex identities are consecutive integers, assigned from arbitrary branch lengths.
Only the two source JSON files supply mathematical data. All graph, multiset,
automorphism, affine, insertion and reduced-witness checks are implemented here.
Run with Python 3.10+; writes audit-results.json beside this file.
"""

from collections import Counter
from dataclasses import dataclass
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "graceful-k7-feasibility"


def demand(condition, message):
    if not condition:
        raise ValueError(message)


@dataclass(frozen=True)
class Tree:
    adjacency: tuple

    @property
    def order(self):
        return len(self.adjacency)

    @property
    def edges(self):
        return tuple((u, v) for u, ns in enumerate(self.adjacency)
                     for v in sorted(ns) if u < v)


def tree_from_edges(order, edges):
    adjacency = [set() for _ in range(order)]
    for u, v in edges:
        demand(0 <= u < order and 0 <= v < order and u != v, "invalid edge")
        demand(v not in adjacency[u], "duplicate edge")
        adjacency[u].add(v)
        adjacency[v].add(u)
    graph = Tree(tuple(frozenset(ns) for ns in adjacency))
    demand(len(graph.edges) == order - 1, "tree edge count")
    reached, frontier = set(), [0]
    while frontier:
        u = frontier.pop()
        if u not in reached:
            reached.add(u)
            frontier.extend(adjacency[u] - reached)
    demand(len(reached) == order, "disconnected graph")
    return graph


def spider(lengths):
    """Create the entire graph from lengths, not from certificate field names."""
    edges, branches, next_vertex = [], [], 1
    for length in lengths:
        demand(type(length) is int and length >= 1, "invalid branch length")
        branch = tuple(range(next_vertex, next_vertex + length))
        branches.append(branch)
        edges.append((0, branch[0]))
        edges.extend(zip(branch, branch[1:]))
        next_vertex += length
    return tree_from_edges(next_vertex, edges), tuple(branches)


def audit(graph, labels, attachment=0, threshold=None, zero=None):
    q = graph.order - 1
    demand(len(labels) == graph.order, "label vector length")
    demand(all(type(x) is int for x in labels), "nonintegral label")
    demand(Counter(labels) == Counter(range(q + 1)), "vertex multiset")
    differences = Counter(abs(labels[u] - labels[v]) for u, v in graph.edges)
    demand(differences == Counter(range(1, q + 1)), "edge multiset")
    if zero is not None:
        demand(labels[zero] == 0, "wrong zero vertex")
    if threshold is None:
        return None
    demand(type(threshold) is int and 0 <= threshold <= q, "threshold domain")
    c = labels[attachment]
    d = c - threshold if c > threshold else threshold + 1 - c
    same, cross = Counter(), Counter()
    for u, v in graph.edges:
        target = same if (labels[u] <= threshold) == (labels[v] <= threshold) else cross
        target[abs(labels[u] - labels[v])] += 1
    demand(same == Counter(range(1, d)), "same-side multiset")
    demand(cross == Counter(range(d, q + 1)), "crossing multiset")
    return d


def complement(labels, threshold):
    q = len(labels) - 1
    return tuple(q - x for x in labels), q - 1 - threshold


def gap_extend(graph, labels, threshold, count, attachment=0, reverse=False):
    """Insert an entire gap at once, independently of the source recurrence."""
    demand(type(count) is int and count >= 0, "negative insertion count")
    old = tuple(x + count * (x > threshold) for x in labels)
    gap = tuple(range(threshold + 1, threshold + count + 1))
    if reverse:
        gap = tuple(reversed(gap))
    edges = graph.edges + tuple((attachment, v)
                                for v in range(graph.order, graph.order + count))
    return tree_from_edges(graph.order + count, edges), old + gap


def certify_affine_identity(graph, labels, threshold):
    """Coefficients in n=m-1: every old difference is b+a*n, b>0,a>=0."""
    d = audit(graph, labels, threshold=threshold)
    vertex_polynomials = [(x, int(x > threshold)) for x in labels]
    edge_polynomials = Counter()
    records = []
    for u, v in graph.edges:
        lo, hi = (u, v) if labels[u] < labels[v] else (v, u)
        b = vertex_polynomials[hi][0] - vertex_polynomials[lo][0]
        a = vertex_polynomials[hi][1] - vertex_polynomials[lo][1]
        demand(b > 0 and a >= 0, "absolute-value sign is not uniform for n>=0")
        edge_polynomials[(b, a)] += 1
        records.append({"vertices": [u, v], "difference": b, "n_coefficient": a})
    expected = Counter((e, 0) for e in range(1, d))
    expected.update((e, 1) for e in range(d, graph.order))
    demand(edge_polynomials == expected, "affine old-edge identity")
    # In three coefficients (constant,n,s), the s-th new leaf is t+s,
    # 1<=s<=n. Choose the edge's sign from the attachment's threshold side.
    c = labels[0]
    center_poly = (c, int(c > threshold), 0)
    leaf_poly = (threshold, 0, 1)
    sign = 1 if c > threshold else -1
    new_edge = tuple(sign * (x - y) for x, y in zip(center_poly, leaf_poly))
    expected_new = (d, 1, -1) if c > threshold else (d - 1, 0, 1)
    demand(new_edge == expected_new, "symbolic new-edge identity")
    # The minimum over 1<=s<=n is d in either case; n=0 is empty.
    demand(d >= 1 and d <= graph.order, "interval endpoint domain")
    return records, list(new_edge)


def verify_complement(graph, labels, threshold, attachment=0):
    demand(threshold < graph.order - 1, "complement requires t<=q-1")
    transformed, new_threshold = complement(labels, threshold)
    demand(all((x <= threshold) != (y <= new_threshold)
               for x, y in zip(labels, transformed)), "complement side reversal")
    old_d = audit(graph, labels, attachment, threshold)
    new_d = audit(graph, transformed, attachment, new_threshold)
    demand(old_d == new_d, "complement changes d")
    demand(complement(transformed, new_threshold) == (labels, threshold), "involution")
    return transformed, new_threshold


def orbit_partition_and_transport(m, rows):
    graph, branches = spider([7, 7, 7] + [1] * m)
    # Rooted distances separate depths; degree separates short leaves from
    # long-arm depth 1. Explicit generators prove transitivity inside each cell.
    expected = {frozenset([0]), frozenset(b[0] for b in branches[3:])}
    expected.update(frozenset(branches[a][depth] for a in range(3)) for depth in range(7))
    parent = list(range(graph.order))

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    def accept_permutation(p):
        demand(sorted(p) == list(range(graph.order)), "nonpermutation")
        moved_edges = {tuple(sorted((p[u], p[v]))) for u, v in graph.edges}
        demand(moved_edges == set(graph.edges), "not a graph automorphism")
        for u, v in enumerate(p):
            parent[find(u)] = find(v)

    for a, b in ((0, 1), (1, 2)):
        p = list(range(graph.order))
        for u, v in zip(branches[a], branches[b]):
            p[u], p[v] = v, u
        accept_permutation(p)
    for j in range(3, len(branches) - 1):
        p = list(range(graph.order))
        u, v = branches[j][0], branches[j + 1][0]
        p[u], p[v] = v, u
        accept_permutation(p)
    cells = {}
    for v in range(graph.order):
        cells.setdefault(find(v), set()).add(v)
    demand({frozenset(cell) for cell in cells.values()} == expected, "nine orbit cells")
    # Audit a transported labeling with zero at EVERY vertex for these m.
    for target in range(graph.order):
        if target == 0:
            role, p = "center", list(range(graph.order))
        elif target >= 22:
            role, p = "leaf", list(range(graph.order))
            p[22], p[target] = target, 22
        else:
            a, depth = divmod(target - 1, 7)
            role, p = f"arm{depth + 1}", list(range(graph.order))
            for u, v in zip(branches[0], branches[a]):
                p[u], p[v] = v, u
        base, threshold = rows[role]
        extended, values = gap_extend(spider([7, 7, 7, 1])[0], base,
                                      threshold, m - 1, reverse=True)
        demand(extended == graph, "extended graph differs from reconstructed spider")
        transported = [None] * graph.order
        for u, x in enumerate(values):
            transported[p[u]] = x
        audit(graph, tuple(transported), threshold=threshold, zero=target)
    return graph.order


def exhaustive_small_insertion():
    """All gracefully labeled trees with 1..7 edges, up to vertex-label identity.

    Choose one edge of each difference: there are exactly q! candidate edge
    sets. Every graceful tree on the labels 0..q occurs; disconnected sets are
    excluded. Every attachment vertex and integer threshold is considered.
    This is a diagnostic, not the proof of the general lemma.
    """
    totals = Counter()
    for q in range(1, 8):
        options = [tuple((x, x + delta) for x in range(q + 1 - delta))
                   for delta in range(1, q + 1)]
        for chosen in product(*options):
            totals["candidate_edge_sets"] += 1
            try:
                graph = tree_from_edges(q + 1, chosen)
            except ValueError as error:
                demand(str(error) == "disconnected graph", "unexpected candidate failure")
                continue
            labels = tuple(range(q + 1))
            audit(graph, labels)
            totals["graceful_trees"] += 1
            for threshold in range(q + 1):
                same = Counter(abs(u - v) for u, v in graph.edges
                               if (u <= threshold) == (v <= threshold))
                for attachment in range(q + 1):
                    d = attachment - threshold if attachment > threshold else threshold + 1 - attachment
                    if same != Counter(range(1, d)):
                        continue
                    audit(graph, labels, attachment, threshold)
                    totals["valid_invariants"] += 1
                    totals["high_attachment" if attachment > threshold else "low_attachment"] += 1
                    if threshold == q:
                        totals["t_equals_q"] += 1
                    else:
                        verify_complement(graph, labels, threshold, attachment)
                        totals["complements"] += 1
                    for n in (1, 2, 5):
                        grown, values = gap_extend(graph, labels, threshold, n, attachment)
                        audit(grown, values, attachment, threshold, zero=0)
                        totals["insertions"] += 1
    return dict(totals)


def check_reduced_seed(data, arm7):
    seed = data["tip_reduction_seed"]
    graph, branches = spider([7, 7, 1])
    values = (seed["center"], *seed["arms"][0], *seed["arms"][1], seed["leaf"])
    audit(graph, values)
    demand(seed["center"] == 15, "reduced center must be maximum")
    r, q = 3, 22
    extra_arm = tuple(r - depth // 2 if depth % 2 == 0 else q - r + 1 + depth // 2
                      for depth in range(2 * r + 1))
    lifted = (values[0] + r + 1, *extra_arm,
              *(x + r + 1 for x in values[1:]))
    demand(lifted == arm7[0], "odd-arm lift does not recover full tip certificate")
    audit(spider([7, 7, 7, 1])[0], lifted, threshold=r, zero=7)
    # Separately check k=1 (r=0), including the empty high-label part of the arm.
    reduced_k1 = (3, 0, 1, 2)
    audit(spider([1, 1, 1])[0], reduced_k1)
    lifted_k1 = (4, 0, 1, 2, 3)
    base_k1 = spider([1, 1, 1, 1])[0]
    audit(base_k1, lifted_k1, threshold=0, zero=1)
    for m in (1, 2, 3, 17):
        grown, values = gap_extend(base_k1, lifted_k1, 0, m - 1)
        audit(grown, values, threshold=0, zero=1)
    # The new-arm formulas work without reference to any reduced witness.
    # Check r=0..100 to catch indexing errors; the algebraic proof is in README.
    for r in range(101):
        q, c = 6 * r + 4, 5 * r + 4
        arm = tuple(r - j // 2 if j % 2 == 0 else q - r + 1 + j // 2
                    for j in range(2 * r + 1))
        demand(Counter(arm) == Counter(list(range(r + 1)) + list(range(5 * r + 5, 6 * r + 5))), "tip label blocks")
        differences = tuple(abs(x - y) for x, y in zip((c,) + arm, arm))
        demand(differences == tuple(range(4 * r + 4, 6 * r + 5)), "tip edge order")
    return {"k7_lift": "PASS", "k1_separate": "PASS", "arm_formula_r_0_to_100": "PASS"}


def main():
    input_files = ("bases.json", "continuation-bases.json", "continuation.md", "README.md", "verify-continuation.py", "verify.py")
    hashes = {name: sha256((SOURCE / name).read_bytes()).hexdigest() for name in input_files}
    old = json.loads((SOURCE / "bases.json").read_text(encoding="utf-8"))
    new = json.loads((SOURCE / "continuation-bases.json").read_text(encoding="utf-8"))
    demand(set(old["seeds"]) == {"leaf"}, "unexpected old seed set")
    demand(set(new["seeds"]) == {"arm1", "arm3", "arm5", "arm7"}, "unexpected new seed set")
    demand(old["complements"] == {"center": "leaf"}, "old complement mapping")
    demand(new["complements"] == {"arm2": "arm1", "arm4": "arm3", "arm6": "arm5"}, "new complement mapping")
    graph, branches = spider([7, 7, 7, 1])
    rows = {}
    for data in (old, new):
        demand(data["family"] == "S(7,7,7,1^m)" and data["base_m"] == 1 and data["q"] == 22, "metadata")
        for role, seed in data["seeds"].items():
            demand(len(seed["arms"]) == 3 and [len(a) for a in seed["arms"]] == [7] * 3, "seed geometry")
            values = (seed["center"], *(x for arm in seed["arms"] for x in arm), seed["p0"])
            rows[role] = (values, seed["threshold"])
        for role, origin in data["complements"].items():
            rows[role] = verify_complement(graph, *rows[origin])
    roles = ("center", *(f"arm{depth}" for depth in range(1, 8)), "leaf")
    demand(set(rows) == set(roles), "incomplete orbit family")
    results = {}
    sample_ms = (1, 2, 3, 8, 64, 257)
    for role in roles:
        values, t = rows[role]
        zero = 0 if role == "center" else 22 if role == "leaf" else int(role[3:])
        d = audit(graph, values, threshold=t, zero=zero)
        polynomial_records, new_edge = certify_affine_identity(graph, values, t)
        verify_complement(graph, values, t)
        cut = None
        if values[0] > t:
            low = {v for v, x in enumerate(values) if x <= t}
            ell = sum(len(graph.adjacency[v]) == 1 for v in low)
            internal = sum(u in low and v in low for u, v in graph.edges)
            cut_size = sum((u in low) != (v in low) for u, v in graph.edges)
            demand(cut_size == 2 * len(low) - ell - 2 * internal, "cut degree identity")
            demand(22 - values[0] == len(low) - ell - 2 * internal, "cut invariant identity")
            cut = {"low_vertices": len(low), "low_leaves": ell, "low_low_edges": internal, "cut_size": cut_size}
        for m in sample_ms:
            rebuilt, _ = spider([7, 7, 7] + [1] * m)
            grown, labels = gap_extend(graph, values, t, m - 1, reverse=True)
            demand(rebuilt == grown, "graph mismatch for m")
            audit(rebuilt, labels, threshold=t, zero=zero)
        recurrence = values
        for m in range(2, 13):
            recurrence = tuple(x + int(x > t) for x in recurrence) + (t + 1,)
            direct = gap_extend(graph, values, t, m - 1, reverse=True)[1]
            demand(recurrence == direct, "source closed formula differs from one-leaf recurrence")
        results[role] = {"center": values[0], "threshold": t, "d": d,
                         "zero_vertex": zero, "labels_by_vertex": values,
                         "edges": polynomial_records, "new_leaf_difference_coefficients_1_n_s": new_edge,
                         "cut": cut, "sample_m": sample_ms}
        print(f"{role}: PASS, center={values[0]}, t={t}, d={d}, all-n affine certificate")
    all_vertex_cases = sum(orbit_partition_and_transport(m, rows) for m in (1, 2, 5))
    reduction = check_reduced_seed(new, rows["arm7"])
    # Threshold corruption must be rejected independently of gracefulness.
    caught = False
    try:
        audit(graph, rows["arm7"][0], threshold=2, zero=7)
    except ValueError:
        caught = True
    demand(caught, "negative control was not rejected")
    # For t=2,c=19, a zero tip leaves at most 1+2+2 crossing edges,
    # while the requested interval 17..22 contains six.
    demand(1 + 2 * 2 < len(range(19 - 2, 23)), "claimed cut obstruction")
    small = exhaustive_small_insertion()
    for name, before in hashes.items():
        demand(sha256((SOURCE / name).read_bytes()).hexdigest() == before, "source changed during audit")
    output = {"verdict": "GO", "theorem": "S(7,7,7,1^m) is 0-rotatable for every integer m>=1",
              "source_sha256": hashes, "vertex_numbering": "center 0; long arms 1..7,8..14,15..21; short leaves 22,...",
              "base_edges": graph.edges, "orbits": results,
              "explicit_extended_labelings": len(roles) * len(sample_ms),
              "all_vertex_transport_checks": all_vertex_cases,
              "odd_arm_reduction": reduction, "exhaustive_small_tree_diagnostics": small,
              "complement_boundary": "zero-preserving threshold domain requires 0<=t<=q-1; all supplied bases satisfy this",
              "novelty_assessed": False}
    (HERE / "audit-results.json").write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(f"All nine orbits: PASS; {all_vertex_cases} explicit transports to every vertex.")
    print("Odd-arm reduction, k=1 boundary, cut obstruction, corruption control: PASS.")
    print("Exhaustive small-tree diagnostics:", json.dumps(small, sort_keys=True))
    print("GO for mathematical statement; novelty not assessed.")


if __name__ == "__main__":
    main()
