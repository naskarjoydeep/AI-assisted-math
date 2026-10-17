import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Algebra.Order.Star.Pi
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Theorem A: Kitaev's approximate factorization on an arbitrary Hilbert space (statement)

Source: `kitaev_almost_idempotent/note/infinite_dim.tex`, Theorem A, which extends
A. Kitaev, arXiv:2405.02434v2, Theorem 12.3 from `dim H < ∞` to Hilbert spaces of any dimension,
under the hypothesis that `Φ̃ = θ(2Φ - 1)` has finite rank.

Six results are **assumed** (named hypotheses of `Claim`, never axioms): three textbook facts
about completely positive maps (`CPMapFacts`, `StinespringThm`, `UnitaryDesign`) and three results
of Kitaev's paper (Theorem 12.1, equation (12.6), Theorem 10.5). Everything else is proved.

`open scoped ComplexOrder` only switches on Mathlib's standard partial order on `ℂ`
(`z ≤ w ↔ re z ≤ re w ∧ im z = im w`), which Mathlib's matrix C*-norm requires.
-/

open scoped ComplexOrder

noncomputable section

namespace Cert.KitaevChannels

/-- `M_n(M)`: `n × n` matrices over a C*-algebra `M`, with Mathlib's C*-norm and order. -/
abbrev Mat (n : ℕ) (M : Type*) : Type _ := CStarMatrix (Fin n) (Fin n) M

/-- The finite-dimensional C*-algebra `⊕_{j<m} M_{d_j}(ℂ)`. -/
abbrev BlockAlg {m : ℕ} (d : Fin m → ℕ) : Type := (j : Fin m) → Mat (d j) ℂ

/-- `‖φ‖_cb ≤ c`: every amplification `1_{M_n} ⊗ φ` (apply `φ` entrywise to an `n × n`
matrix) has norm at most `c`. -/
def CBBound {M₁ M₂ : Type*} [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
    [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂] (φ : M₁ →ₗ[ℂ] M₂) (c : ℝ) : Prop :=
  ∀ (n : ℕ) (X : Mat n M₁), ‖X.map φ‖ ≤ c * ‖X‖

/-- `φ` is completely positive: every amplification maps positive matrices to positive matrices
(the defining condition of Mathlib's `CompletelyPositiveMap`). -/
def IsCP {M₁ M₂ : Type*} [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
    [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂] (φ : M₁ →ₗ[ℂ] M₂) : Prop :=
  ∀ (n : ℕ) (X : Mat n M₁), 0 ≤ X → 0 ≤ X.map φ

/-- `φ` is unital completely positive. -/
def IsUCP {M₁ M₂ : Type*} [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
    [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂] (φ : M₁ →ₗ[ℂ] M₂) : Prop :=
  φ 1 = 1 ∧ IsCP φ

/-- Kitaev (12.2): `Φ̃ = θ(2Φ-1) = ½(1 + (2Φ-1)(1 - 4(Φ-Φ²))^{-1/2})`, with
`(1-x)^{-1/2} = ∑ₖ (2k choose k)/4ᵏ · xᵏ`, in the Banach algebra of bounded maps on `B(H)`. -/
def tildePhi {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  (1 / 2 : ℂ) • (1 + (2 • Φ - 1) *
    ∑' k : ℕ, ((Nat.centralBinom k : ℂ) / 4 ^ k) • (4 • (Φ - Φ * Φ)) ^ k)

/-- Kitaev (12.5): the approximate Choi–Effros product `X ⋆ Y = Φ̃(XY)`. -/
def choiEffros {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) :
    (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
  (LinearMap.mul ℂ (H →L[ℂ] H)).compr₂ (tildePhi Φ).toLinearMap

/-- The matrix product over a bilinear (possibly non-associative) product `mul`:
`(X ⋆ Y)ᵢⱼ = ∑ₗ mul (Xᵢₗ) (Yₗⱼ)` (Kitaev §10). -/
def matMul {M : Type*} [AddCommMonoid M] [Module ℂ M] (mul : M →ₗ[ℂ] M →ₗ[ℂ] M) {n : ℕ}
    (X Y : Mat n M) : Mat n M :=
  CStarMatrix.ofMatrix (fun i j => ∑ l, mul (X i l) (Y l j))

/-- Kitaev's extended ε-C* algebra (§10), realized concretely inside `B(H)`, with exact unit:
a subspace `A ∋ 1` closed under `†` and under the bilinear product `mul`, with
`(X ⋆ Y)† = Y† ⋆ X†` and `X ⋆ 1 = X = 1 ⋆ X`, such that for every `n` the space `M_n(A)`, with
the norm of `M_n(B(H))`, the entrywise involution and the matrix product over `mul`, satisfies
(2.1), (2.2) and (2.5). (The remaining axioms (2.4), (2.6) hold automatically in `M_n(B(H))`.) -/
def ExtEpsCStarSub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ε : ℝ) (A : Submodule ℂ (H →L[ℂ] H))
    (mul : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) : Prop :=
  (1 : H →L[ℂ] H) ∈ A ∧ (∀ x ∈ A, star x ∈ A) ∧ (∀ x ∈ A, ∀ y ∈ A, mul x y ∈ A) ∧
  (∀ x ∈ A, ∀ y ∈ A, star (mul x y) = mul (star y) (star x)) ∧
  (∀ x ∈ A, mul x 1 = x ∧ mul 1 x = x) ∧
  ∀ (n : ℕ) (X Y Z : Mat n (H →L[ℂ] H)),
    (∀ i j, X i j ∈ A) → (∀ i j, Y i j ∈ A) → (∀ i j, Z i j ∈ A) →
    ‖matMul mul X Y‖ ≤ (1 + ε) * ‖X‖ * ‖Y‖ ∧
    ‖matMul mul (matMul mul X Y) Z - matMul mul X (matMul mul Y Z)‖ ≤ ε * ‖X‖ * ‖Y‖ * ‖Z‖ ∧
    (1 - ε) * ‖X‖ ^ 2 ≤ ‖matMul mul (star X) X‖

/-- Kitaev's extended δ-isomorphism (§10) from `⊕ⱼ M_{dⱼ}(ℂ)` onto `(A, mul)`: a linear bijection
onto `A` commuting with `†`, with `‖v(I) - I‖ ≤ δ`, and at every matrix level `n`
`‖v(XY) - v(X) ⋆ v(Y)‖ ≤ δ‖X‖‖Y‖` and `(1-δ)‖X‖ ≤ ‖v(X)‖ ≤ (1+δ)‖X‖`. -/
def IsExtDeltaIsoOnto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m : ℕ} {d : Fin m → ℕ} (δ : ℝ) (A : Submodule ℂ (H →L[ℂ] H))
    (mul : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (v : BlockAlg d →ₗ[ℂ] (H →L[ℂ] H)) : Prop :=
  Function.Injective v ∧ LinearMap.range v = A ∧
  (∀ b, v (star b) = star (v b)) ∧ ‖v 1 - 1‖ ≤ δ ∧
  ∀ (n : ℕ) (X Y : Mat n (BlockAlg d)),
    ‖(X * Y).map v - matMul mul (X.map v) (Y.map v)‖ ≤ δ * ‖X‖ * ‖Y‖ ∧
    (1 - δ) * ‖X‖ ≤ ‖X.map v‖ ∧ ‖X.map v‖ ≤ (1 + δ) * ‖X‖

/-- **Assumed (textbook): completely positive maps.** For a CP map `φ` between unital
C*-algebras, `‖φ‖_cb = ‖φ(1)‖` (Paulsen, *Completely bounded maps and operator algebras*,
Prop. 3.6), and `φ` commutes with the involution (positive maps are self-adjoint). -/
def CPMapFacts : Prop :=
  ∀ (M₁ M₂ : Type) [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
    [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂] (φ : M₁ →ₗ[ℂ] M₂),
    IsCP φ → CBBound φ ‖φ 1‖ ∧ ∀ x, φ (star x) = star (φ x)

/-- **Assumed (textbook): Stinespring's theorem** (Stinespring 1955; Paulsen Thm. 4.1 and the
easy converse): a linear map `φ : M → B(H)` from a unital C*-algebra is completely positive iff
`φ(x) = V† π(x) V` for a unital *-representation `π` of `M` on some Hilbert space `K` and a
bounded `V : H → K`. -/
def StinespringThm : Prop :=
  ∀ (M : Type) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : M →ₗ[ℂ] (H →L[ℂ] H)),
    IsCP φ ↔ ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K),
      ∀ x, φ x = (ContinuousLinearMap.adjoint V) ∘L (π x) ∘L V

/-- **Assumed (textbook): unitary 1-designs** (e.g. the generalized Pauli group): for every `d`
there is a finite probability distribution `p` on unitaries `U s` of `M_d(ℂ)` with the twirl
identity `∑ₛ pₛ (Uₛ†)ₐᵦ (Uₛ)꜀ₑ = δₐₑ δᵦ꜀ / d`. -/
def UnitaryDesign : Prop :=
  ∀ d : ℕ, ∃ (S : Type) (_ : Fintype S) (p : S → ℝ) (U : S → Mat d ℂ),
    (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1 ∧ (∀ s, star (U s) * U s = 1 ∧ U s * star (U s) = 1) ∧
    ∀ a b c e : Fin d, ∑ s, (p s : ℂ) * star (U s b a) * U s c e =
      if a = e ∧ b = c then 1 / (d : ℂ) else 0

/-- **Assumed: Kitaev, Theorem 12.1** (proved there for Hilbert spaces of any dimension, §12.1):
for an η-idempotent UCP map, `Im Φ̃` with the product `Φ̃(XY)` is an extended `O(η)`-C* algebra. -/
def Kitaev12_1 (c₁ η₁ : ℝ) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (η : ℝ),
    IsUCP Φ.toLinearMap → CBBound (Φ * Φ - Φ).toLinearMap η → 0 ≤ η → η < η₁ →
    ExtEpsCStarSub (c₁ * η) (LinearMap.range (tildePhi Φ).toLinearMap) (choiEffros Φ)

/-- **Assumed: Kitaev, equation (12.6)** (proved there for any dimension, applied to `1_{M_n} ⊗ Φ`):
`Φ(Φ(Φ(X)Φ(Y))Φ(Z)) = Φ(Φ(X)Φ(Y)Φ(Z)) + O(η)‖X‖‖Y‖‖Z‖`. -/
def Kitaev12_6 (c₂ η₂ : ℝ) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (η : ℝ),
    IsUCP Φ.toLinearMap → CBBound (Φ * Φ - Φ).toLinearMap η → 0 ≤ η → η < η₂ →
    ∀ (n : ℕ) (X Y Z : Mat n (H →L[ℂ] H)),
      ‖(((X.map Φ * Y.map Φ).map Φ) * Z.map Φ).map Φ - (X.map Φ * Y.map Φ * Z.map Φ).map Φ‖
        ≤ c₂ * η * ‖X‖ * ‖Y‖ * ‖Z‖

/-- **Assumed: Kitaev, Theorem 10.5**, for extended ε-C* algebras realized inside some `B(H)`,
with the C*-algebra in the block form `⊕ⱼ M_{dⱼ}(ℂ)` that Kitaev's proof constructs (§9). -/
def Kitaev10_5 (C₃ ε₃ : ℝ) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (A : Submodule ℂ (H →L[ℂ] H)) [FiniteDimensional ℂ A]
    (mul : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) (ε : ℝ),
    0 ≤ ε → ε < ε₃ → ExtEpsCStarSub ε A mul →
    ∃ (m : ℕ) (d : Fin m → ℕ) (v : BlockAlg d →ₗ[ℂ] (H →L[ℂ] H)),
      IsExtDeltaIsoOnto (C₃ * ε) A mul v

/-- **Theorem A.** Assume the three textbook facts above, and Kitaev's Theorem 12.1, (12.6) and
Theorem 10.5 (with their constants).
Then there are universal constants `η₀ > 0` and `C` such that for every nonzero Hilbert space `H`
of any dimension and every UCP map `Φ` on `B(H)` with `‖Φ² - Φ‖_cb ≤ η < η₀` and `Φ̃` of finite
rank, there are a block algebra `B = ⊕ⱼ M_{dⱼ}(ℂ)` and
(i) an extended `(C η)`-isomorphism `v : B → (Im Φ̃, ⋆)`, in particular a linear bijection, and
(ii) UCP maps `Δ : B → B(H)`, `Υ : B(H) → B` with `‖ΔΥ - Φ‖_cb ≤ C η` and
`‖Υₙ(Δₙ(X) Δₙ(Y)) - XY‖ ≤ C η ‖X‖‖Y‖` for all `n` and `X, Y ∈ Mₙ(B)`. -/
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

end Cert.KitaevChannels
