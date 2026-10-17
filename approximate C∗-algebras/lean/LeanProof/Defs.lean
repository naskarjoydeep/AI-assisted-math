import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Kitaev's ε-C* algebras and δ-isomorphisms

Definitions from A. Kitaev, *Almost-idempotent quantum channels and approximate C*-algebras*,
arXiv:2405.02434, Section 2 (Definitions 2.1 and 2.2), transcribed verbatim.

An ε-C* algebra is a complex Banach space with a bilinear (not necessarily associative)
multiplication, a conjugate-linear isometric involution, and an approximate unit, satisfying
Kitaev's axioms (2.1)–(2.6).
-/

open scoped ComplexConjugate

noncomputable section

namespace Kitaev

/-- Kitaev's ε-C* algebra structure on a complex normed space `A`
(arXiv:2405.02434, Definition 2.1, with the default approximate unit (2.6)).
Completeness of `A` is a separate `CompleteSpace` hypothesis where needed. -/
structure EpsCStar (ε : ℝ) (A : Type*) [NormedAddCommGroup A] [NormedSpace ℂ A] where
  /-- the (bilinear, possibly non-associative) product -/
  mul : A → A → A
  mul_add : ∀ x y z, mul x (y + z) = mul x y + mul x z
  add_mul : ∀ x y z, mul (x + y) z = mul x z + mul y z
  mul_smul : ∀ (c : ℂ) (x y : A), mul x (c • y) = c • mul x y
  smul_mul : ∀ (c : ℂ) (x y : A), mul (c • x) y = c • mul x y
  /-- the involution `X ↦ X†` -/
  star : A → A
  star_add : ∀ x y, star (x + y) = star x + star y
  star_smul : ∀ (c : ℂ) (x : A), star (c • x) = conj c • star x
  star_star : ∀ x, star (star x) = x
  /-- (2.4): the involution is isometric -/
  norm_star : ∀ x, ‖star x‖ = ‖x‖
  /-- (2.4): `(XY)† = Y† X†` -/
  star_mul : ∀ x y, star (mul x y) = mul (star y) (star x)
  /-- the (approximate) unit `I` -/
  one : A
  star_one : star one = one
  /-- (2.1) -/
  norm_mul_le : ∀ x y, ‖mul x y‖ ≤ (1 + ε) * ‖x‖ * ‖y‖
  /-- (2.2): ε-associativity -/
  assoc_le : ∀ x y z, ‖mul (mul x y) z - mul x (mul y z)‖ ≤ ε * ‖x‖ * ‖y‖ * ‖z‖
  /-- (2.5): approximate C* identity -/
  cstar_le : ∀ x, (1 - ε) * ‖x‖ ^ 2 ≤ ‖mul (star x) x‖
  /-- (2.6) -/
  mul_one_le : ∀ x, ‖mul x one - x‖ ≤ ε * ‖x‖
  /-- (2.6) -/
  one_mul_le : ∀ x, ‖mul one x - x‖ ≤ ε * ‖x‖
  /-- (2.6) -/
  norm_one_le : |‖one‖ - 1| ≤ ε

/-- A δ-isomorphism (arXiv:2405.02434, Definition 2.2): a linear bijection that commutes with the
involution, preserves the unit and the product up to δ, and distorts norms by at most `1 ± δ`. -/
structure DeltaIso (δ : ℝ) {A A' : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup A'] [NormedSpace ℂ A'] {ε ε' : ℝ}
    (S : EpsCStar ε A) (S' : EpsCStar ε' A') where
  /-- the underlying linear bijection -/
  toEquiv : A ≃ₗ[ℂ] A'
  map_star : ∀ x, toEquiv (S.star x) = S'.star (toEquiv x)
  /-- (2.8) -/
  map_one_le : ‖toEquiv S.one - S'.one‖ ≤ δ
  /-- (2.9) -/
  map_mul_le : ∀ x y, ‖toEquiv (S.mul x y) - S'.mul (toEquiv x) (toEquiv y)‖ ≤ δ * ‖x‖ * ‖y‖
  /-- δ-inclusion, lower bound -/
  le_norm_map : ∀ x, (1 - δ) * ‖x‖ ≤ ‖toEquiv x‖
  /-- δ-inclusion, upper bound -/
  norm_map_le : ∀ x, ‖toEquiv x‖ ≤ (1 + δ) * ‖x‖

/-- Every (unital, nonzero) C*-algebra is a 0-C* algebra. -/
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

/-- **Kitaev's Theorem 2.3**, stated as a proposition with explicit constants:
every finite-dimensional ε-C* algebra with `0 ≤ ε < ε₀` is `(C ε)`-isomorphic to a C*-algebra.
This file does *not* prove it; it is used only as an explicit hypothesis. -/
def KitaevFiniteDim (C ε₀ : ℝ) : Prop :=
  ∀ (A : Type) [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    [FiniteDimensional ℂ A] (ε : ℝ) (S : EpsCStar ε A), 0 ≤ ε → ε < ε₀ →
    ∃ (B : Type) (_ : CStarAlgebra B) (_ : Nontrivial B),
      Nonempty (DeltaIso (C * ε) (ofCStarAlgebra B) S)

end Kitaev
