# Kitaev's ε-C\* rigidity beyond finite dimensions

This repository has two parts: a short paper on how far Kitaev's theory of almost-idempotent quantum channels ([arXiv:2405.02434](https://arxiv.org/abs/2405.02434)) extends to infinite-dimensional Hilbert spaces, and a Lean 4 formalization of its two positive results.

| Path | Content |
|---|---|
| [`paper/`](paper/) | The paper, as PDF and as a single LaTeX source that compiles with `pdflatex` |
| [`lean/`](lean/) | Lean 4 + Mathlib sources, the audit script, and [`LEAN_CERTIFICATE.md`](lean/LEAN_CERTIFICATE.md) with the formal statements, assumptions and audit record |

Both formal results are **conditional**. The results of Kitaev's paper they rely on, and three textbook facts about completely positive maps, are explicit hypotheses of the formal statements, not axioms. To check the proofs, install Lean with [elan](https://github.com/leanprover/elan) and run:

```bash
cd lean
lake exe cache get
lake build
lake env lean Check.lean
python3 audit.py KitaevChannels
python3 audit.py KitaevSectors
```
