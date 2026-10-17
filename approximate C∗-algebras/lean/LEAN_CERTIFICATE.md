# Lean certificates: Kitaev's ε-C\* rigidity beyond finite dimensions

Machine-checked certificates for the two positive results of the paper [`kitaev_rigidity_infinite_dim.pdf`](../paper/kitaev_rigidity_infinite_dim.pdf). The Lean sources are in this folder; [`README.md`](README.md) explains how to build and audit them.
Equation and theorem numbers such as (12.37) or Theorem 2.3 refer to A. Kitaev, *Almost-idempotent quantum channels and approximate C\*-algebras*, arXiv:2405.02434v2.

| Result | Lean certificate | Status | Audit |
|---|---|---|---|
| **Theorem A**: Kitaev's approximate factorization Φ ≈ ΔΥ through a C\* algebra, on a Hilbert space of any dimension, when Φ̃ has finite rank | `Cert.KitaevChannels.main` in `Certs/KitaevChannels/` (19 modules, about 3,600 lines) | CONDITIONAL: 6 named assumptions | PASS, 2026-10-16T11:48:58+0800 |
| **Theorem B**: ℓ^∞-sums of finite-dimensional ε-C\* algebras are Cε-isomorphic to C\* algebras | `Cert.KitaevSectors.main` in `Certs/KitaevSectors/` (3 modules) | CONDITIONAL: 1 named assumption (Kitaev's Theorem 2.3) | PASS, 2026-10-16T11:49:20+0800 |

## How to read a certificate

A reader who wants to rely on a certificate needs to trust three things, and none of them is the proof.

1. **The formal statement** says what the paper says. Each part below prints it verbatim, with a dictionary from Lean to mathematics. It is also the file `Statement.lean`, which contains definitions only.
2. **The assumptions** are the cited results, faithfully stated. They are explicit hypotheses of the statement `Claim`, never `axiom`s. A certificate is CONDITIONAL exactly when such hypotheses are present.
3. **The Lean kernel** is sound.

The audit (`audit.py`) checks everything else mechanically, in this order:
- a scan of every source file, with comments and strings stripped, for `sorry`, `admit`, `axiom`, `native_decide` and similar escape hatches;
- a full build of every module;
- a type check that `main` proves *exactly* `Claim`, via a generated `example : Claim := main`;
- `#print axioms` for `main` and for every non-vacuity theorem, where only Lean's standard `propext`, `Classical.choice` and `Quot.sound` are allowed;
- an independent replay of every module by `leanchecker`.

Both certificates passed all five checks on the toolchain `leanprover/lean4:v4.35.0-rc4` with Mathlib `1f414401f69059aa7eead47b53ee40bd38455eeb`.

---

## Part I. Theorem A: approximate factorization on a Hilbert space of any dimension

**Status:** CONDITIONAL (6 assumptions: three textbook facts about completely positive maps, and Kitaev's Theorem 12.1, equation (12.6) and Theorem 10.5)
**Source:** the paper ([`kitaev_rigidity_infinite_dim.pdf`](../paper/kitaev_rigidity_infinite_dim.pdf)), Theorem A. That theorem extends A. Kitaev, *Almost-idempotent quantum channels and approximate C\*-algebras*, arXiv:2405.02434v2, Theorem 12.3, from `dim H < ∞` to Hilbert spaces of arbitrary dimension.

### Informal statement

There are universal constants η₀, C > 0 with the following property. Let H be a nonzero Hilbert space of arbitrary dimension and Φ: B(H) → B(H) a UCP map with ‖Φ² − Φ‖_cb ≤ η ≤ η₀ such that Φ̃ has finite rank. Then

(i) there are a finite-dimensional C\* algebra B and an extended Cη-isomorphism v: B → A = Im Φ̃; in particular v is a linear bijection;

(ii) there are UCP maps Δ: B → B(H) and Υ: B(H) → B with ‖ΔΥ − Φ‖_cb ≤ Cη and ‖Υₙ(Δₙ(X)Δₙ(Y)) − XY‖ ≤ Cη‖X‖‖Y‖ for all n and X, Y ∈ Mₙ ⊗ B.

### Formal statement (`Statement.lean`, sha256 `b6a7086255f9…`)

```lean
def Claim : Prop :=
  CPMapFacts → StinespringThm → UnitaryDesign →
  ∀ (c₁ η₁ c₂ η₂ C₃ ε₃ : ℝ), 0 ≤ c₁ → 0 < η₁ → 0 ≤ c₂ → 0 < η₂ → 0 ≤ C₃ → 0 < ε₃ →
  Kitaev12_1 c₁ η₁ → Kitaev12_6 c₂ η₂ → Kitaev10_5 C₃ ε₃ →
  ∃ (η₀ C : ℝ), 0 < η₀ ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (η : ℝ),
    IsUCP Φ.toLinearMap → CBBound (Φ * Φ - Φ).toLinearMap η → 0 ≤ η → η < η₀ →
    FiniteDimensional ℂ (LinearMap.range (tildePhi Φ).toLinearMap) →
    ∃ (m : ℕ) (d : Fin m → ℕ) (v : BlockAlg d →ₗ[ℂ] (H →L[ℂ] H))
      (Δ : BlockAlg d →ₗ[ℂ] (H →L[ℂ] H)) (Υ : (H →L[ℂ] H) →ₗ[ℂ] BlockAlg d),
      IsExtDeltaIsoOnto (C * η) (LinearMap.range (tildePhi Φ).toLinearMap) (choiEffros Φ) v ∧
      IsUCP Δ ∧ IsUCP Υ ∧
      CBBound (Δ ∘ₗ Υ - Φ.toLinearMap) (C * η) ∧
      ∀ (n : ℕ) (X Y : Mat n (BlockAlg d)),
        ‖(X.map Δ * Y.map Δ).map Υ - X * Y‖ ≤ C * η * ‖X‖ * ‖Y‖
```

The proof produces explicit constants: with Λ = C₃c₁ + c₂ + 1, it takes η₀ = min(η₁, η₂, ε₃/(c₁+1), 1/(2·10⁵ Λ)) and C = 10⁶ Λ.

### Dictionary

| Lean | Meaning | Note |
|---|---|---|
| `H →L[ℂ] H` | B(H), bounded operators on a complex Hilbert space of any dimension | Mathlib's C\*-algebra structure; no separability or dimension assumption |
| `Mat n M` | Mₙ(M) with Mathlib's `CStarMatrix` C\*-norm and order | The norm of Mₙ(B(H)) is the operator norm on Hⁿ |
| `BlockAlg d` | ⊕_{j<m} M_{d_j}(ℂ) | Every finite-dimensional C\*-algebra is of this form (Artin–Wedderburn). Blocks with d_j = 0 are allowed and handled |
| `CBBound φ c` | ‖φ‖_cb ≤ c: every amplification `X ↦ X.map φ` has norm ≤ c | The definition of the cb norm, written as a bound so that no supremum is needed |
| `IsCP`, `IsUCP` | complete positivity (every amplification preserves `0 ≤`), plus φ(1) = 1 | The defining condition of Mathlib's `CompletelyPositiveMap` |
| `tildePhi Φ` | Kitaev (12.2), ½(1 + (2Φ−1)(1−4(Φ−Φ²))^{-1/2}), the square root as the binomial series | Converges for η < 1/4 (`Tilde.lean`); as a `tsum` it would be junk-valued otherwise, but `η₀ ≤ 1/(2·10⁵)` keeps it convergent |
| `choiEffros Φ` | the approximate Choi–Effros product X ⋆ Y = Φ̃(XY), Kitaev (12.5) | |
| `ExtEpsCStarSub ε A mul` | Kitaev §10: A is an extended ε-C\* algebra inside B(H) | Axioms (2.1), (2.2), (2.5) at every matrix level, an exact unit, and the involution. (2.4) and (2.6) are automatic for the norm of Mₙ(B(H)) |
| `IsExtDeltaIsoOnto δ A mul v` | Kitaev §10: an extended δ-isomorphism onto A | Injective, range A, †-preserving, ‖v(1) − 1‖ ≤ δ, and at every level ‖v(XY) − v(X)⋆v(Y)‖ ≤ δ‖X‖‖Y‖ and (1−δ)‖X‖ ≤ ‖vX‖ ≤ (1+δ)‖X‖ |
| `η < η₀` | the paper's η ≤ η₀ | The same theorem with a smaller η₀ |
| `FiniteDimensional ℂ (range Φ̃)` | Φ̃ has finite rank | The hypothesis of Theorem A, verbatim |

### Assumptions

| Hypothesis | Source | Faithfulness of the formal version |
|---|---|---|
| `CPMapFacts` | Paulsen, *Completely Bounded Maps and Operator Algebras*, Prop. 3.6; positive maps are self-adjoint | Exact. A CP map between unital C\*-algebras has ‖φ‖_cb = ‖φ(1)‖, and φ(x\*) = φ(x)\*. Only the inequality ‖φ‖_cb ≤ ‖φ(1)‖ is used |
| `StinespringThm` | Stinespring 1955; Paulsen Thm. 4.1, with the easy converse | Exact for maps into B(H). The dilation space K is required to live in `Type`, which Stinespring's construction satisfies |
| `UnitaryDesign` | e.g. the Weyl–Heisenberg (generalized Pauli) group | Exact: a finite probability distribution on unitaries of M_d(ℂ) satisfying the twirl identity. For d = 0 it holds trivially |
| `Kitaev12_1 c₁ η₁` | Kitaev, Theorem 12.1 (proved there for H of any dimension, §12.1) | Matches. Im Φ̃ with ⋆ is an extended (c₁η)-C\* algebra whenever Φ is UCP with ‖Φ² − Φ‖_cb ≤ η < η₁. The O(η) is made explicit as c₁η |
| `Kitaev12_6 c₂ η₂` | Kitaev, (12.6), applied to 1_{Mₙ} ⊗ Φ | Matches, with the O(η) explicit as c₂η, at every matrix level |
| `Kitaev10_5 C₃ ε₃` | Kitaev, Theorem 10.5 | Matches for extended ε-C\* algebras realized inside some B(H), with the C\*-algebra written in block form ⊕ M_{d_j}(ℂ). The block form costs nothing, since it is how Kitaev's §9 builds B. Not formalized: its proof is Kitaev's finite-dimensional rigidity theory (Lefschetz–Hopf, H-spaces, the implicit function theorem) |

### Non-vacuity

`Sanity.lean` proves `hyps_satisfiable_infinite_dim`. On ℓ²(ℕ), which is nontrivial and not finite-dimensional, the map Φ(X) = ⟨e₀, X e₀⟩·1 is UCP and exactly idempotent, so ‖Φ² − Φ‖_cb ≤ η for every η ≥ 0. Its Φ̃ = Φ has rank one. So every hypothesis of `Claim` on (H, Φ, η) holds in a genuinely infinite-dimensional H, which is the setting of Theorem A. Complete positivity is proved from scratch (`statePhi_cp`). Φₙ(Y\*Y) is a sum of Gram matrices tensored with 1, and each of those is a sum of Z\*Z, by Mathlib's `posSemidef_gram` and `posSemidef_iff_eq_sum_vecMulVec`.

The conclusion is not degenerate. v is a linear bijection onto Im Φ̃ (injective, with range exactly Im Φ̃), and Δ and Υ are UCP. The bounds then force Υ∘Δ ≈ 1_B and Δ∘Υ ≈ Φ.

Nothing here shows that the six assumptions are jointly satisfiable for some constants. For the three of Kitaev's, that is the content of his paper.

### Step map

| Informal step | Lean lemma | Notes (what the formal version needed that the text skipped) |
|---|---|---|
| ‖Φ̃ − Φ‖_cb = O(η) | `tildePhi_sub_cb` (Tilde) | Explicit constant 12η for η ≤ 1/8. The series is summed in the Banach algebra of bounded maps, with cb bounds passed through the `tsum` |
| (12.25)–(12.27): Υ̃ = v⁻¹Φ̃, Δ̃Υ̃ = Φ̃, Υ̃Δ̃ = 1 | `upsTilde`, `v_upsTilde`, `upsTilde_v`, `upsTilde_cb` (Objects) | ‖Υ̃‖_cb ≤ (1+12η)/(1−δ) from the lower bound of v |
| Diagonal of ⊕ M_{d_j} as an average over unitaries | `Design.diag`, `cross_vanish`, `diag_block` (Design) | **Repaired**, see Findings: independent signs ±1 per block |
| Δ′ = Σ pₛ Φ(Δ̃(·uₛ\*)Δ̃(uₛ)) is CP and ‖Δ′ − Δ̃‖_cb = O(η) | `DeltaP_cp`, `DeltaP_sub_cb` (Delta) | Positivity of Mₙ(BlockAlg) is generated by Y\*Y (`StarOrderedRing.nonneg_iff`) |
| Δ = Δ′(1)^{-1/2}Δ′Δ′(1)^{-1/2} is UCP, ‖Δ − Δ̃‖_cb = O(η) | `exists_normalizer` (Normalize), `exists_Delta` (DeltaUCP) | Inverse square root by the continuous functional calculus, with ‖c − 1‖ ≤ 2‖a − 1‖ |
| (12.34), (12.35), (12.36) at every level n | `phi_delta_cb`, `mul35`, `mul36` (DeltaProps) | (12.36) uses (12.6) at level n, exactly as Kitaev does |
| Stinespring Δ = W\*ρ(·)W replaces the Choi form (12.37) | `StinespringThm`, applied in `main` | Dimension-free. Kitaev's Choi form needs dim H < ∞ |
| Lemma 12.4: R commutes with ρ(M_{d_j}), 1 − O(η) ≤ ‖R‖ ≤ 1 | `Rop_comm`, `Rop_isSelfAdjoint`, `Rop_norm_ge` (Stine, Lemma124), `Rop_norm_le` (UpsBlock) | No tensor factorization R = 1 ⊗ C is needed. Commutation with the matrix units is enough |
| Choose ξ_j with ‖C_jξ_j‖ ≈ 1 | `norm_le_norm_comp_P`, `exists_zeta` (Zeta) | ‖R‖ ≤ ‖R P₀₀‖ by a Pythagoras sum over rows, then ζ ∈ Im P₀₀ with ‖Rζ‖ ≥ ‖R‖ − τ. The norm need not be attained when dim E_j = ∞ |
| U ⊗ ξ_j, and (1⊗ξ\*)R(Y⊗1)R(1⊗ξ) = ‖Cξ‖²Y | `Jop`, `J_sandwich`, `T_sandwich`, `norm_J_le` (Zeta) | J e_b = P_{b0}ζ plays the role of 1 ⊗ ξ |
| Choi form of Φ replaced by Stinespring Φ = V\*π(·)V; L_j and Υ′_j | `Bop`, `Lop`, `compress_L` (UpsBlock) | The first line of Kitaev's computation of Υ′_j(Δ(Y)), as an exact identity |
| Kitaev's chain for Υ′_j(Δ(Y)) ≈ Y_j, at every level | `sandwich_cb`, `Delta_sum`, `ups_delta_eq`, `block_bound` (UpsBlock) | The identity is proved as an equality of linear maps, so amplification is automatic. A† · B is cb-bounded by polarization (`compress_cb`) |
| Υ′ ≈ Υ′Φ ≈ Υ′Φ̃ = Υ′Δ̃Υ̃ ≈ Υ′ΔΥ̃ ≈ Υ̃, then normalization | `upsPrime`, `upsPrime_close`, `exists_Ups` (Upsilon) | ⊕ M_{d_j} is nontrivial because ‖v(1) − 1‖ ≤ δ < 1 |
| (ii): ΔΥ ≈ Φ and Υₙ(ΔₙXΔₙY) ≈ XY | `final_bounds` (Final) | ΔΥ − Φ = (Δ − v)Υ + v(Υ − Υ̃) + (Φ̃ − Φ), and Υ̃(ΔXΔY) is compared with XY through the lower bound of v |
| η = 0 | `upsTilde_ucp_exact`, `nonneg_of_unital_isometry` (Final) | Step (d) of the paper's proof, added after formalization; see Findings |
| Constants | `arith_delta`, `arith_main` (Arith), `main` (Proof) | Every O(η) is an explicit multiple of Λη |

### What was not checked

The six assumptions, in particular Kitaev's Theorems 10.5 and 12.1 and equation (12.6), which carry the deep part of the finite-dimensional theory. Part (i) of Theorem A is exactly Theorem 10.5 applied to Im Φ̃, so the formal content of (i) is that the hypotheses of 10.5 are met. The paper's Lemma 2.1 (finite rank of Φ implies finite rank of Φ̃), its remark on the Riesz projection, and Corollary 2.4 on codes are outside the formal claim. The constants (C = 10⁶Λ) are deliberately crude. Kitaev's theorem leaves its O(η) unspecified, and nothing was optimized.

### Findings

The diagonal of a block algebra in Kitaev's §8 and §12.2 is built as the product of per-block unitary designs, and that product is not a diagonal once there are two or more blocks. Already for ℂ ⊕ ℂ with trivial designs the average is I ⊗ I, not the diagonal Σ eⱼ ⊗ eⱼ. The cross-block terms survive because they carry the first moments Σ pₛ Uₛ, which do not vanish. The formal proof repairs this by attaching an independent uniform sign ±1 to each block. Every cross-block term then averages to zero (`cross_vanish`), and the per-block twirl identity gives the diagonal property that the rest of the argument uses (`diag_block`). Only Δ′ depends on this, and the repaired Δ′ satisfies everything Kitaev needs, so the theorem is unaffected. The paper records the correction in the proof of Theorem A.

Kitaev's proof uses two Choi representations, (12.37) for Δ and Φ(X) = V\*(X ⊗ 1)V for Φ. The second exists only for normal Φ, so it fails in general once dim H = ∞. The formal proof replaces both with Stinespring dilations, as the paper proposes. The replacement for R_j = 1 ⊗ C_j turned out not to need any tensor factorization: commutation of R with the matrix units of block j is enough to run Lemma 12.4 and Kitaev's final computation.

When dim E_j = ∞ the norm of C_j need not be attained, and the first version of the paper picked ξ_j with ‖C_jξ_j‖ ≥ ‖C_j‖ − η. That choice is unavailable at η = 0, where the theorem asks for an exact factorization. The formal proof runs the approximate-maximizer argument only for η > 0, with slack τ = η. At η = 0 it argues separately. Then δ = 0, so v is a unital complete isometry, and a unital isometry reflects positivity of self-adjoint elements (‖t − y‖ ≤ t forces y ≥ 0). Hence Υ̃ = v⁻¹Φ̃ is itself UCP, and every error term vanishes. The paper contains this argument as step (d) of the proof of Theorem A.

On paper, a simpler repair also seems to work, though it is not formalized (it is the remark after Theorem A in the paper): any ξ_j with ‖C_jξ_j‖ ≥ 1/2 suffices. The per-block factor ‖C_jξ_j‖² is central in ⊕ M_{d_j}, and the normalization Υ′(1)^{-1/2}(·)Υ′(1)^{-1/2} divides it out up to O(η).

One technical point. Mathlib synthesizes the complex continuous functional calculus on Mₙ(⊕ M_{d_j}(ℂ)), but not the real one for self-adjoint elements. The positivity arguments were therefore stated for an abstract C\*-algebra and then applied, which is also how `exists_normalizer` is used.

---

## Part II. Theorem B: infinitely many finite sectors

**Status:** CONDITIONAL (1 assumption: Kitaev's Theorem 2.3, the finite-dimensional theorem)
**Source:** the paper ([`kitaev_rigidity_infinite_dim.pdf`](../paper/kitaev_rigidity_infinite_dim.pdf)), Proposition 3.1 and the first sentence of Theorem B. Definitions and the assumed theorem are from A. Kitaev, *Almost-idempotent quantum channels and approximate C\*-algebras*, arXiv:2405.02434v2: Definitions 2.1–2.2 and Theorem 2.3.

### Informal statement

Let ε₀, C be the constants of Kitaev's Theorem 2.3. Every ℓ^∞-direct sum of finite-dimensional ε-C\* algebras with 0 ≤ ε < ε₀ and Cε < 1 is Cε-isomorphic to a C\* algebra. That is, there is a linear bijection v: B → ⊕^∞ A_i from a genuine C\* algebra B that commutes with the involution, preserves unit and product up to Cε, and distorts norms by at most 1 ± Cε. With infinitely many nonzero sectors the direct sum is infinite-dimensional.

### Formal statement (`Statement.lean`, sha256 `552f06db05a4…`)

```lean
def Claim : Prop :=
  ∀ (C ε₀ : ℝ), KitaevFiniteDim C ε₀ →
  ∀ (ε : ℝ), 0 ≤ ε → ε < ε₀ → C * ε < 1 →
  ∀ (ι : Type) [Nonempty ι] (A : ι → Type) [∀ i, NormedAddCommGroup (A i)]
    [∀ i, NormedSpace ℂ (A i)] [∀ i, FiniteDimensional ℂ (A i)]
    (S : ∀ i, EpsCStar ε (A i)) (T : EpsCStar ε (lp A ∞)),
    (∀ f g i, T.mul f g i = (S i).mul (f i) (g i)) →
    (∀ f i, T.star f i = (S i).star (f i)) →
    (∀ i, T.one i = (S i).one) →
    ∃ (B : Type) (_ : CStarAlgebra B) (_ : Nontrivial B),
      Nonempty (DeltaIso (C * ε) (ofCStarAlgebra B) T)
```

### Dictionary

| Lean | Meaning | Note |
|---|---|---|
| `EpsCStar ε A` | Kitaev's Def. 2.1: an ε-C\* structure on a complex normed space | Fields are the axioms verbatim: bilinear product (not assumed associative), conjugate-linear isometric involution with `(XY)† = Y†X†`, unit with `I† = I`, (2.1) `‖XY‖ ≤ (1+ε)‖X‖‖Y‖`, (2.2) `‖(XY)Z − X(YZ)‖ ≤ ε‖X‖‖Y‖‖Z‖`, (2.5) `(1−ε)‖X‖² ≤ ‖X†X‖`, (2.6) `‖XI − X‖, ‖IX − X‖ ≤ ε‖X‖`, `|‖I‖ − 1| ≤ ε` |
| `DeltaIso δ S S'` | Kitaev's Def. 2.2: a δ-isomorphism (bijective δ-inclusion) | `toEquiv : A ≃ₗ[ℂ] A'` is the linear bijection; the other fields are (2.8), (2.9), commutation with †, and `(1−δ)‖X‖ ≤ ‖v X‖ ≤ (1+δ)‖X‖` |
| `ofCStarAlgebra B` | a C\*-algebra's own product, involution and unit, as a 0-C\* structure | Defined, not characterized |
| `CStarAlgebra B`, `Nontrivial B` | Mathlib's unital complete complex C\*-algebra, with `1 ≠ 0` | Kitaev assumes `I ≠ 0` throughout |
| `KitaevFiniteDim C ε₀` | Kitaev's Theorem 2.3 with explicit constants | The assumption (see below) |
| `lp A ∞` | Mathlib's ℓ^∞-direct sum: bounded families, supremum norm | |
| the three coordinate hypotheses on `T` | "`T` is the direct-sum ε-C\* structure" | Stated as formulas rather than as a construction, so the statement file contains no construction. `Sanity.lean` shows such `T` exist |
| `ι : Type`, `A : ι → Type` | sectors in universe 0 | Kitaev's theorem is then assumed only for universe-0 algebras, which is a weaker assumption |
| `C * ε < 1` | ε small enough that a Cε-isomorphism is invertible with bounded inverse | Equivalent to using the threshold min(ε₀, 1/C) in place of ε₀; see Findings |

The statement has no division, square roots, sums or limits, so it has no junk-value traps. All scalars are ℂ (Kitaev's algebras are complex); norms and constants are ℝ.

### Assumptions

| Hypothesis | Source | Faithfulness of the formal version |
|---|---|---|
| `KitaevFiniteDim C ε₀`: every finite-dimensional ε-C\* algebra with 0 ≤ ε < ε₀ admits a `(C ε)`-isomorphism from some nonzero C\*-algebra | Kitaev, Theorem 2.3 ("Any finite-dimensional ε-C\* algebra is O(ε)-isomorphic to some C\* algebra B", universal constant) | Matches, with three harmless differences. (i) The O(ε) and "ε sufficiently small" are made explicit as C and ε₀, and `Claim` quantifies over every pair for which the theorem holds. (ii) `A` is required to be complete, as in Kitaev's definition; this is automatic in finite dimension. (iii) Only universe-0 algebras are covered. Each of these makes the assumption no stronger than Kitaev's theorem. Its proof (Lefschetz–Hopf on the approximate unitary group, H-space theory, the implicit function theorem) is not formalized; Mathlib lacks that algebraic topology |

### Non-vacuity

`Sanity.lean` proves three things.

- `hyps_satisfiable`: for every ε ≥ 0 the sector and coordinate hypotheses hold with countably many sectors (ι = ℕ, every A i = ℂ).
- `sum_not_finiteDimensional`: that direct sum is not finite-dimensional, so `Claim` genuinely covers infinite-dimensional ε-C\* algebras.
- `kitaev_hypothesis_exact_case`: at ε = 0 the conclusion of the assumed hypothesis is a theorem. The transcribed axioms with ε = 0 rebuild every field of Mathlib's `CStarAlgebra`, and the identity is then a 0-isomorphism. This checks the transcription of Definitions 2.1–2.2 against Mathlib's C\*-algebras.

What cannot be shown here is that `KitaevFiniteDim C ε₀` holds for some ε₀ > 0. That is Kitaev's theorem itself.

### Step map

| Informal step | Lean lemma | Notes |
|---|---|---|
| S1. Apply Kitaev's theorem to each sector | `step1`, `choose` in `main` | Kitaev's hypothesis is stated for Banach spaces, so the step needs `FiniteDimensional.complete` (finite-dimensional normed spaces over ℂ are complete), which the text uses silently. The choice of one `B i` and `v i` per sector uses `Classical.choice` |
| S2. ℓ^∞(B) is a C\*-algebra | `lpCStarAlgebra`, `step2_nontrivial` | Mathlib provides every field. Nontriviality needs a nonempty index set |
| S3. The coordinatewise map is a linear bijection | `step3_equiv` | This is where Cε < 1 is used. The inverse family has norm at most ‖g‖/(1 − Cε), uniformly in the sector |
| S4. The δ-inequalities pass to suprema | `step4_deltaIso` | Each bound holds coordinatewise with the same δ, and `lp.norm_le_of_forall_le` takes the supremum |
| assembly | `main` | Also derives 0 ≤ Cε from `0 ≤ ‖v(I) − I‖ ≤ Cε`, so no hypothesis 0 ≤ C is needed |

### What was not checked

- Kitaev's Theorem 2.3 itself: it is the assumption.
- Theorem A of the paper: it has its own certificate (Part I).
- The second sentence of Theorem B (the channel statement), which combines this certificate with Theorem A sector by sector.
- The extended (operator-space) version of the sector theorem, the ultraproduct remark, and the open general case.

### Findings

The proof is correct as written. Formalizing it made four of its quiet assumptions explicit.

1. **The condition Cε < 1 is genuinely needed.** For a single finite-dimensional algebra any Cε-isomorphism is a bijection. Across infinitely many sectors, though, the inverses must be bounded uniformly, and that requires 1 − Cε > 0. Without it the coordinatewise map need not be onto ℓ^∞. Since Kitaev's theorem with threshold ε₀ implies it with threshold min(ε₀, 1/C), the condition costs nothing.
2. **The index set must be nonempty.** An empty direct sum is the zero space, which violates |‖I‖ − 1| ≤ ε for ε < 1. This is Kitaev's standing assumption I ≠ 0.
3. **No sign hypothesis on C is needed.** It follows from the existence of any δ-isomorphism.
4. **Kitaev's remark holds formally.** An ε-C\* algebra with ε = 0 "is the same as a C\* algebra": the transcribed axioms at ε = 0 yield a Mathlib `CStarAlgebra`.

---

## Part III. Other formal results

The library `LeanProof` in [`LeanProof/`](LeanProof/) is an earlier project on the same toolchain and Mathlib. It contains two further results. It builds cleanly, and `#print axioms` reports only the standard axioms (see `Check.lean`), but it was not run through the certificate audit.

- `Kitaev.DeltaIso.symm`: the inverse of a δ-isomorphism is a δ/(1−δ)³-isomorphism. This is Kitaev's "δ + O(δ²)" with an explicit constant.
- `Kitaev.Graded.graded_rigidity`: the paper's Proposition 4.3 (graded rigidity of twisted group algebras), in full.

## Audit record

Theorem A: PASS at 2026-10-16T11:48:58+0800. Axioms of `main` and of all 8 non-vacuity theorems: propext, Classical.choice, Quot.sound. `leanchecker` passed on all 19 modules.

Theorem B: PASS at 2026-10-16T11:49:20+0800. Axioms of `main` and of all 9 non-vacuity theorems: propext, Classical.choice, Quot.sound. `leanchecker` passed on all 3 modules.

The sources in this folder are byte-identical to the audited ones, with the SHA-256 hashes below. They were also built and audited as a standalone copy of this folder: both PASS (Theorem A at 2026-10-16T12:06:56+0800, Theorem B at 2026-10-16T12:07:20+0800), with the same hashes.

<details>
<summary>SHA-256 of the audited sources</summary>

| `KitaevChannels` file | SHA-256 |
|---|---|
| `Statement.lean` | `b6a7086255f94b4baf06ddc00f4c52b541bf4b68cada763c8dc85703f96417a5` |
| `Proof.lean` | `2b4708255626db0461cf13a08d696b92271e59f656ff5fda2957db833d3f46e7` |
| `Sanity.lean` | `eae5f53892b1b118ca11f4764c72fa33860e15c6b7ab7c66c464d7fa7280dc9f` |
| `Arith.lean` | `59a946bf3987db9df32d9d2efffa525b20ce1bac5daa1c3ea21947b7e5228bc2` |
| `Delta.lean` | `01cd54d71973ccb2bc2cc9c7ea10f93b95d5b1db2a94b1329991f7638c4c67df` |
| `DeltaProps.lean` | `76599f76831680efa15b3ddc7828eeb95f2a119f3523162818b847a4c6edc51c` |
| `DeltaUCP.lean` | `03850153cc55790cad1e61db15437e362df191b740ed4ce504429c75eb0c95e2` |
| `Design.lean` | `6b10cafa832b41a431aab1f0420cd4293692a6c88e6e45d8f02380e476c787e3` |
| `Final.lean` | `ee39e5a36c316270d7369df3e7cb55341faef0f65bb2e03538e49a027b18695e` |
| `Lemma124.lean` | `378f2162b7b8913035f6bcc367a3d196f475776b6c4c0e127e7774005f75cecb` |
| `Normalize.lean` | `1f5d1639df6a94c4b4a5fde1802e134fb2c1aff2f72026e4953018e719530d55` |
| `Objects.lean` | `e8bbabb7c1fff8341794871b16dae9982ffcc9e1ccfed53700cc6bd1a58e2552` |
| `Plumbing.lean` | `b9b0d08391c0345d67de87ce715bfb9ebbf9f673b129cbca325645129132c3ca` |
| `Stine.lean` | `3fc975542ce1d523623e9c0fe212f84d56176529ff39c005fe4a603fc4913027` |
| `Tilde.lean` | `f92f7e1873755fafb36f79f9d1ee0b6cce460bc146a01cf10bb79385f66556db` |
| `Toolkit.lean` | `5f3e38d7bb70cb4d90723931b36f6e26a55b8516cb2cace0d542e856e39e40f4` |
| `UpsBlock.lean` | `98323816af5ec84efccbfc2d3489b17f6bd87445b94ea2f1d4193d8af2734086` |
| `Upsilon.lean` | `4a5c64c5a5e3125858c26a8bd22a382d63d8258c88d24ed779e7a8a566afcb3f` |
| `Zeta.lean` | `caf5d2b286821a420c1baaa3e043d773e2eb3d1d5b487f363364241b444fee93` |

| `KitaevSectors` file | SHA-256 |
|---|---|
| `Statement.lean` | `552f06db05a4dec26a6c25873796fc6034fba5e1848926262dfca810f34de59c` |
| `Proof.lean` | `1d36731b86abe6427a6e4238943de04e4bf697967389897312fe03bfb0d45090` |
| `Sanity.lean` | `e70e885cf940585ff174f39953731ca6d6391c32c5f8a7465dba05f85390d3a9` |

</details>

## Reproducing

With [elan](https://github.com/leanprover/elan) installed:

```bash
lake exe cache get
lake build
lake env lean Check.lean
python3 audit.py KitaevChannels
python3 audit.py KitaevSectors
```

`Check.lean` confirms that each `main` proves exactly its `Claim`, and prints the axioms of the main results. Each audit ends with `PASS` and writes `Certs/<Name>/audit.json`, whose file hashes should match the table above. Do not run `lake update`: the proofs are checked against the pinned Mathlib commit.
