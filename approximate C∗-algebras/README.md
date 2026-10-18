# Kitaev's ε-C\* rigidity beyond finite dimensions

**Authors:** Joydeep Naskar (Beijing Institute of Mathematical Sciences and Applications, BIMSA) and Claude (Anthropic).

A short paper on how far Kitaev's theory of almost-idempotent quantum channels ([arXiv:2405.02434](https://arxiv.org/abs/2405.02434)) extends once the Hilbert space is infinite-dimensional, with a Lean 4 verification of its two positive results.

| File | What it is |
|---|---|
| [`kitaev_rigidity_infinite_dim.pdf`](kitaev_rigidity_infinite_dim.pdf) | The paper (8 pages) |
| [`lean_certificate.pdf`](lean_certificate.pdf) | The Lean certificates: formal statements, assumptions, a map from the proofs to the Lean code, findings, and the audit record (18 pages) |
| [`lean_sources.zip`](lean_sources.zip) | The Lean 4 + Mathlib sources, as one Lake project with a check file and the audit script |

## Why it matters

Many physical systems hide a smaller, protected system inside a larger one: a quantum error-correcting code hides its logical qubits, and in holography a bulk region is encoded in the boundary. In practice the encoding is never exact. What one has is a channel Φ that is nearly a projection, ‖Φ² − Φ‖_cb ≤ η. Kitaev showed that such a channel determines a logical algebra: the image of a smoothed version Φ̃ carries an approximately associative product, it is O(η)-close to a genuine C\* algebra 𝓑, and Φ approximately factors as Φ ≈ ΔΥ through 𝓑. His theorems assume finite dimension, which excludes bosonic codes, quantum field theory and holographic codes, where the Hilbert space is infinite-dimensional.

## What the paper shows

**Theorem A.** If the Hilbert space is infinite-dimensional but the logical algebra is finite-dimensional, as for an oscillator code with finitely many logical qubits, Kitaev's bijection and his factorization Φ ≈ ΔΥ both hold, with the same universal constants. His proof uses finite dimension only through two Choi representations, and both can be replaced by Stinespring dilations.

**Theorem B.** If the almost-invariant algebra is an ℓ^∞-sum of finite-dimensional pieces, the results survive too, because Kitaev's constants are uniform. For a block-diagonal channel Φ = ⊕ₖ Φₖ(Pₖ · Pₖ), the factorization holds through an infinite-dimensional C\* algebra.

**The general case is open.** The paper identifies the three places where Kitaev's proof needs a finite-dimensional algebra, shows that no counterexample can be seen on finitely many elements, and points to degree-3 bounded cohomology of non-amenable groups as the likely source of one.

## What is verified

Both theorems are machine-checked in Lean 4 with Mathlib, in three certificates: one for Theorem A and two for Theorem B. Each passes an audit with no unproved steps, only Lean's three standard axioms, and an independent replay in a second kernel checker. The certificates are **conditional**. The results they do not reprove are stated as explicit hypotheses, not hidden as axioms: Kitaev's Theorems 2.3, 10.5 and 12.1 and his equation (12.6), together with three textbook facts about completely positive maps (Stinespring's theorem, the cb norm of a CP map, and unitary designs).

The formalization caught three problems, and the paper fixes them. The first two are in Kitaev's published argument; the third was in the first draft of our own Theorem B.
- **Kitaev's diagonal is wrong for two or more blocks.** His averaged design is not a diagonal for 𝓑 = ⊕ M_{dⱼ} with several blocks. An independent random sign on each block repairs it.
- **The exact case η = 0 needs its own argument.** In infinite dimensions the relevant operator norm need not be attained.
- **The channel part of Theorem B needs Cη < 1.** Without it, the isomorphisms in the separate blocks need not combine into one.

## Checking the proofs

Install Lean with [elan](https://github.com/leanprover/elan), then run:

```bash
unzip lean_sources.zip
cd lean
lake exe cache get
lake build
lake env lean Check.lean
python3 audit.py KitaevChannels
python3 audit.py KitaevSectors
python3 audit.py KitaevSectorSums
```

`lake exe cache get` downloads a prebuilt Mathlib, so the build takes a few minutes. `Check.lean` should report only `propext`, `Classical.choice` and `Quot.sound`. Each audit should end with `PASS`. Do not run `lake update`: the proofs are checked against the pinned Mathlib commit.

## Caveats

This is a research note and has not been peer-reviewed. The certificates verify every step *given* the cited results of Kitaev's paper, whose own proofs need algebraic topology that Mathlib does not yet have. The constants are deliberately crude.
