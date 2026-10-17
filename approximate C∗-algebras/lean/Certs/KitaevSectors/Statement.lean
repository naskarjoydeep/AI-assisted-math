import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Kitaev's rigidity theorem for infinite-dimensional sector sums (statement)

Source: A. Kitaev, *Almost-idempotent quantum channels and approximate C*-algebras*,
arXiv:2405.02434v2, Definitions 2.1–2.2 and Theorem 2.3; and the companion note
`kitaev_almost_idempotent/note/infinite_dim.tex`, Proposition 3.1 / Theorem B.

Everything Kitaev defines is transcribed literally below. Kitaev's Theorem 2.3 (finite dimension)
is **not** proved here: it appears as the named hypothesis `KitaevFiniteDim C ε₀` of `Claim`.
-/

open scoped ComplexConjugate ENNReal

noncomputable section

namespace Cert.KitaevSectors

/-- Kitaev's Definition 2.1: an ε-C* algebra structure on a complex normed space `A`, with the
default approximate unit (2.6). The product is bilinear but **not** assumed associative. -/
structure EpsCStar (ε : ℝ) (A : Type*) [NormedAddCommGroup A] [NormedSpace ℂ A] where
  /-- the bilinear product `XY` -/
  mul : A → A → A
  mul_add : ∀ x y z, mul x (y + z) = mul x y + mul x z
  add_mul : ∀ x y z, mul (x + y) z = mul x z + mul y z
  mul_smul : ∀ (c : ℂ) (x y : A), mul x (c • y) = c • mul x y
  smul_mul : ∀ (c : ℂ) (x y : A), mul (c • x) y = c • mul x y
  /-- the involution `X ↦ X†` (conjugate linear) -/
  star : A → A
  star_add : ∀ x y, star (x + y) = star x + star y
  star_smul : ∀ (c : ℂ) (x : A), star (c • x) = conj c • star x
  star_star : ∀ x, star (star x) = x
  /-- (2.4) `‖X†‖ = ‖X‖` -/
  norm_star : ∀ x, ‖star x‖ = ‖x‖
  /-- (2.4) `(XY)† = Y†X†` -/
  star_mul : ∀ x y, star (mul x y) = mul (star y) (star x)
  /-- the unit `I`, with `I† = I` -/
  one : A
  star_one : star one = one
  /-- (2.1) `‖XY‖ ≤ (1+ε)‖X‖‖Y‖` -/
  norm_mul_le : ∀ x y, ‖mul x y‖ ≤ (1 + ε) * ‖x‖ * ‖y‖
  /-- (2.2) `‖(XY)Z − X(YZ)‖ ≤ ε‖X‖‖Y‖‖Z‖` -/
  assoc_le : ∀ x y z, ‖mul (mul x y) z - mul x (mul y z)‖ ≤ ε * ‖x‖ * ‖y‖ * ‖z‖
  /-- (2.5) `‖X†X‖ ≥ (1−ε)‖X‖²` -/
  cstar_le : ∀ x, (1 - ε) * ‖x‖ ^ 2 ≤ ‖mul (star x) x‖
  /-- (2.6) `‖XI − X‖ ≤ ε‖X‖` -/
  mul_one_le : ∀ x, ‖mul x one - x‖ ≤ ε * ‖x‖
  /-- (2.6) `‖IX − X‖ ≤ ε‖X‖` -/
  one_mul_le : ∀ x, ‖mul one x - x‖ ≤ ε * ‖x‖
  /-- (2.6) `|‖I‖ − 1| ≤ ε` -/
  norm_one_le : |‖one‖ - 1| ≤ ε

/-- Kitaev's Definition 2.2: a δ-isomorphism is a linear bijection commuting with the involution,
with (2.8) `‖v(I) − I‖ ≤ δ`, (2.9) `‖v(XY) − v(X)v(Y)‖ ≤ δ‖X‖‖Y‖`, and the δ-inclusion bounds
`(1−δ)‖X‖ ≤ ‖v(X)‖ ≤ (1+δ)‖X‖`. -/
structure DeltaIso (δ : ℝ) {A A' : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup A'] [NormedSpace ℂ A'] {ε ε' : ℝ}
    (S : EpsCStar ε A) (S' : EpsCStar ε' A') where
  /-- the linear bijection `v` -/
  toEquiv : A ≃ₗ[ℂ] A'
  map_star : ∀ x, toEquiv (S.star x) = S'.star (toEquiv x)
  map_one_le : ‖toEquiv S.one - S'.one‖ ≤ δ
  map_mul_le : ∀ x y, ‖toEquiv (S.mul x y) - S'.mul (toEquiv x) (toEquiv y)‖ ≤ δ * ‖x‖ * ‖y‖
  le_norm_map : ∀ x, (1 - δ) * ‖x‖ ≤ ‖toEquiv x‖
  norm_map_le : ∀ x, ‖toEquiv x‖ ≤ (1 + δ) * ‖x‖

/-- A genuine (unital, nonzero) C*-algebra, regarded as a 0-C* algebra: its own product,
involution and unit. -/
def ofCStarAlgebra (B : Type*) [CStarAlgebra B] [Nontrivial B] : EpsCStar 0 B where
  mul x y := x * y
  mul_add := mul_add
  add_mul := add_mul
  mul_smul c x y := mul_smul_comm c x y
  smul_mul c x y := smul_mul_assoc c x y
  star := star
  star_add := star_add
  star_smul c x := star_smul c x
  star_star := star_star
  norm_star := norm_star
  star_mul := star_mul
  one := 1
  star_one := star_one B
  norm_mul_le x y := by simpa using norm_mul_le x y
  assoc_le x y z := by simp [mul_assoc]
  cstar_le x := by simp [CStarRing.norm_star_mul_self, sq]
  mul_one_le x := by simp
  one_mul_le x := by simp
  norm_one_le := by simp

/-- **Kitaev's Theorem 2.3 (assumed, not proved here)**, with its constants made explicit:
every finite-dimensional ε-C* algebra with `0 ≤ ε < ε₀` is `(C ε)`-isomorphic to some
(nonzero, unital) C*-algebra `B`. -/
def KitaevFiniteDim (C ε₀ : ℝ) : Prop :=
  ∀ (A : Type) [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    [FiniteDimensional ℂ A] (ε : ℝ) (S : EpsCStar ε A), 0 ≤ ε → ε < ε₀ →
    ∃ (B : Type) (_ : CStarAlgebra B) (_ : Nontrivial B),
      Nonempty (DeltaIso (C * ε) (ofCStarAlgebra B) S)

/-- **Theorem B (infinitely many finite sectors).** If Kitaev's Theorem 2.3 holds with
constants `C, ε₀`, then for every `0 ≤ ε < ε₀` with `C ε < 1`, every nonempty family of
finite-dimensional ε-C* algebras `A i`, and every ε-C* structure `T` on the ℓ^∞-direct sum
`lp A ∞` (bounded families, sup norm) whose product, involution and unit are computed
coordinatewise, there is a C*-algebra `B` and a `(C ε)`-isomorphism `B → (lp A ∞, T)` —
in particular a linear bijection. The direct sum is infinite-dimensional whenever infinitely
many `A i` are nonzero. -/
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

end Cert.KitaevSectors
