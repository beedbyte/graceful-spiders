# Staging verification

This report is generated for the public GitHub staging directory. It distinguishes exact finite checks from the all-`m` proof in the research note.

The two exact checkers are run from the repository root:

```sh
python proof/verify_proof.py
python proof/k4_verify.py
```

The source files were compared with their local, previously published proof-package originals. The language notes were copied from a read-only export of the public Version 1 note. The three project-page links were normalized from site-relative paths to absolute Beedbyte URLs for GitHub; line endings may also differ. Arm length five files and internal audit reports are excluded.

Results and hashes are recorded in `PUBLICATION-MANIFEST.json` after verification.

## Result, 8 October 2026

Both commands passed on the staged copies. The length-three checker verified five base roles and the exact insertion invariant for `m=1,...,100`; the length-four checker verified six base roles over the same range. Their input JSON files and checker source files are byte-identical to the local proof-package sources. The three language notes are GitHub link-adjusted copies of the read-only public Version 1 export; the proof and historical review wording is unchanged. No external dependencies, accounts, or network access were needed.

The `m=1,...,100` runs provide reproducible checks of the certificates and insertion behavior. The induction in the note, not this bounded run, establishes each theorem for all `m >= 1`.
