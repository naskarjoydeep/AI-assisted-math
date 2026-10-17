# Lean sources

Lean 4 + Mathlib sources for the paper [`../paper/kitaev_rigidity_infinite_dim.pdf`](../paper/kitaev_rigidity_infinite_dim.pdf). The certificates (formal statements, assumptions, step map, findings and audit record) are in [`LEAN_CERTIFICATE.md`](LEAN_CERTIFICATE.md). This is one Lake project, pinned to Lean `v4.35.0-rc4` and Mathlib commit `1f414401f69059aa7eead47b53ee40bd38455eeb` (see `lean-toolchain` and `lake-manifest.json`).

## Layout

| Path | Content |
|---|---|
| `Certs/KitaevChannels/` | **Theorem A**: Kitaev's approximate factorization Φ ≈ ΔΥ on a Hilbert space of any dimension (19 modules) |
| `Certs/KitaevSectors/` | **Theorem B**: ℓ^∞-sums of finite-dimensional ε-C\* algebras (3 modules) |
| `LeanProof/` | The earlier project: Kitaev's Definitions 2.1–2.2, the inverse of a δ-isomorphism, and graded rigidity (Proposition 4.3 of the paper) |
| `Check.lean` | Checks that each `main` proves exactly its `Claim`, and prints the axioms of the main results |
| `audit.py` | The full audit: source scan, build, type match, axioms, and `leanchecker` kernel replay |

In each certificate directory, read three files.
- `Statement.lean` is the claim. It contains definitions only, and is what a reader has to check against the paper.
- `Proof.lean` proves `theorem main : Claim`.
- `Sanity.lean` shows that the hypotheses can be met, so the claim is not vacuous.

The remaining modules of `KitaevChannels` are the steps of the proof, in the order of Kitaev's §12.2. The step map in `LEAN_CERTIFICATE.md` links each one to the text.

## Checking

Install Lean with [elan](https://github.com/leanprover/elan), then run from the repository root:

```bash
cd lean
lake exe cache get
lake build
lake env lean Check.lean
python3 audit.py KitaevChannels
python3 audit.py KitaevSectors
```

`lake exe cache get` downloads prebuilt Mathlib, so the build itself takes a few minutes. `Check.lean` should report only `propext`, `Classical.choice` and `Quot.sound`. Each audit ends with `PASS` and writes `Certs/<Name>/audit.json`. That file holds the SHA-256 of every source file, which can be compared with the hashes in `LEAN_CERTIFICATE.md`.

Do not run `lake update`. It moves Mathlib to a newer commit, and the proofs are only checked against the pinned one.

## Assumptions

Both theorems are **conditional**. The results they rely on but do not reprove are explicit hypotheses of `Claim` in `Statement.lean`, never `axiom`s. Theorem A assumes Kitaev's Theorems 12.1 and 10.5, his equation (12.6), Stinespring's theorem, the cb-norm of completely positive maps, and the existence of unitary 1-designs. Theorem B assumes Kitaev's Theorem 2.3. `LEAN_CERTIFICATE.md` discusses how faithful each one is.
