# Eleven-edge arms: independently checked extension

For every n>=2,m>=0, S(11^n,1^m) is zero-rotatable. The four exact alpha paths
in `certificates.json` provide the depth pairs (2,3),(4,5),(6,7),(8,9).
Together with the general constructions for depths 1,2,10,11, the center and
short leaves from `../proof.md`, this covers every prescribed vertex.

`proof.md` gives the all-parameter composition argument. Run:

```
python -B check.py
python -B verify_independent.py
```

The first checker checks the exact paths and 1,680 composed prescribed-zero
examples. The separately implemented second checker covers all vertices
for n=2,...,12,m=0,...,7 (7,172 checks), 84 center examples, 48 stress
compositions and three negative controls. It imports none of the original
search or construction implementations and remains active under `python -O`.
It writes `verification.json` beside its source, using package-relative hash keys.
`AUDIT.md` is a disclosed public adaptation of the separately conducted audit.
Original raw-report and original-checker hashes are recorded in `../SOURCE-MANIFEST.json`;
raw reports containing private workspace paths are excluded.

`search.js` is optional; its reproduction commands appear in this directory's
`proof.md`. Exact certificate checking suffices for existence. The original
discovery counts were not independently reproduced. Python checkers require
only the standard library; optional search reproduction requires Node.js.
Run the assertion-based `check.py` without Python optimization (`-O`).

No arbitrary-odd-k, novelty, priority, formal-verification or external-review
claim is made. See `../literature.md` for primary-source overlap and limits.
