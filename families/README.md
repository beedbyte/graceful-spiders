# Equal-arm spider zero-rotatability families

For every `k in {3,5,7,9,11}`, every integer `n>=2`, every integer `m>=0`, and each prescribed vertex of `S(k^n,1^m)`, the proof constructs a graceful labeling with zero at that vertex. Here `n` counts k-edge arms and `m` counts additional center leaves. The boundary `n=2,m=0` is a path with a distinguished midpoint.

For every odd `k>=3`, the proof also covers zero at the center, arm depths `1,2,k-1,k`, and any existing short leaf. The even-k obstruction applies only to the specified alpha-path method; it is not a negative zero-rotatability theorem.

- [Independently audited eleven-edge extension](k11/README.md), [four additional certificates](k11/certificates.json), and [audit](k11/AUDIT.md).
- [Base proof for 3/5/7/9](proof.md), [six certificates](certificates.json), [constructor](construct.py), and [supplied checker](verify.py).
- [Separate agent audit](independent/AUDIT.md), [independent checker](independent/verify_independent.py), and [fresh results](independent/verification.json).
- [Literature](literature.md), [literature audit](LITERATURE-AUDIT.md), [source provenance](SOURCE-README.md), and [extraction instructions](REPRODUCIBILITY.md).

From this directory, using Python 3.10 or later and no third-party packages:

```sh
python -B verify.py
python -B independent/verify_independent.py
python -B k11/check.py
python -B k11/verify_independent.py
python -B construct.py 9 3 1 5
```

The proof uses established center-zero, alpha-amalgamation, and leaf-extension constructions. Ordinary gracefulness of the entire family is known. Earlier results already cover the path cases, two arms with one center leaf, `k=3,n=2` with arbitrary leaves, and uniform three-edge arms. Publication priority is unresolved. The audit is a separate agent review with its own implementation, not external peer review or formal proof-assistant verification.

## Full manuscript copies

- [English](notes/article.en.md)
- [Deutsch](notes/article.de.md)
- [中文](notes/article.zh.md)
- [Editorial source hashes and link adaptations](notes/MANIFEST.json)

These manuscript copies document the previously reviewed 3/5/7/9 statement and remain unchanged while revised five-length manuscripts undergo separate editorial QA. The new proof-only ZIP adds k11 under `families/` and excludes `notes/`. The earlier proof-only ZIP remains unchanged and is the snapshot described in the manuscript manifest. The reproduction guide distinguishes both archive scopes.
