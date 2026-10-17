import Certs.KitaevSectors.Proof
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Non-vacuity and faithfulness checks for `Claim`

1. `hyps_satisfiable`: for every `ε ≥ 0` the hypotheses on the sectors and on `T` can be met,
   with infinitely many sectors (`ι = ℕ`, every `A i = ℂ`).
2. `sum_not_finiteDimensional`: that ℓ^∞-sum is infinite-dimensional, so `Claim` really is a
   statement about infinite-dimensional ε-C* algebras.
3. `kitaev_hypothesis_exact_case`: at `ε = 0` the assumed hypothesis `KitaevFiniteDim` is a
   *theorem*: every exact (ε = 0) ε-C* algebra is a genuine Mathlib `CStarAlgebra`, 0-isomorphic
   to itself. This checks the transcription of Kitaev's Definitions 2.1–2.2 against Mathlib's
   C*-algebras (Kitaev: "an ε-C* algebra for ε = 0 is the same as a C* algebra").
-/

open scoped ENNReal ComplexConjugate

noncomputable section

namespace Cert.KitaevSectors

/-- An ε-C* structure is an ε'-C* structure for every `ε' ≥ ε` (same operations). -/
def EpsCStar.relax {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] {ε ε' : ℝ}
    (S : EpsCStar ε A) (h : ε ≤ ε') : EpsCStar ε' A where
  mul := S.mul
  mul_add := S.mul_add
  add_mul := S.add_mul
  mul_smul := S.mul_smul
  smul_mul := S.smul_mul
  star := S.star
  star_add := S.star_add
  star_smul := S.star_smul
  star_star := S.star_star
  norm_star := S.norm_star
  star_mul := S.star_mul
  one := S.one
  star_one := S.star_one
  norm_mul_le x y := (S.norm_mul_le x y).trans (by gcongr)
  assoc_le x y z := (S.assoc_le x y z).trans (by gcongr)
  cstar_le x := le_trans (by gcongr) (S.cstar_le x)
  mul_one_le x := (S.mul_one_le x).trans (by gcongr)
  one_mul_le x := (S.one_mul_le x).trans (by gcongr)
  norm_one_le := S.norm_one_le.trans h

/-- (1) The hypotheses of `Claim` are satisfiable for every `ε ≥ 0`, with countably many sectors. -/
theorem hyps_satisfiable (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ (S : ℕ → EpsCStar ε ℂ) (T : EpsCStar ε (lp (fun _ : ℕ => ℂ) ∞)),
      (∀ f g i, T.mul f g i = (S i).mul (f i) (g i)) ∧
      (∀ f i, T.star f i = (S i).star (f i)) ∧
      (∀ i, T.one i = (S i).one) :=
  ⟨fun _ => (ofCStarAlgebra ℂ).relax hε, (ofCStarAlgebra (lp (fun _ : ℕ => ℂ) ∞)).relax hε,
    fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- (2) The sector sum in (1) is infinite-dimensional. -/
theorem sum_not_finiteDimensional : ¬ FiniteDimensional ℂ (lp (fun _ : ℕ => ℂ) ∞) := by
  intro hfin
  let e : ℕ → lp (fun _ : ℕ => ℂ) ∞ := fun n => lp.single ∞ n 1
  let coe : lp (fun _ : ℕ => ℂ) ∞ →ₗ[ℂ] (ℕ → ℂ) :=
    { toFun := fun f => (f : ℕ → ℂ), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hli : LinearIndependent ℂ (coe ∘ e) := by
    have : coe ∘ e = fun n => Pi.single n (1 : ℂ) := by
      funext n
      rfl
    rw [this]
    exact Pi.linearIndependent_single_one ℕ ℂ
  have : Finite ℕ := (LinearIndependent.of_comp coe hli).finite_of_isNoetherian
  exact (Infinite.not_finite this).elim

section Exact

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] (S : EpsCStar 0 A)

theorem exact_assoc (x y z : A) : S.mul (S.mul x y) z = S.mul x (S.mul y z) := by
  have h := S.assoc_le x y z
  simp only [zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

theorem exact_mul_one (x : A) : S.mul x S.one = x := by
  have h := S.mul_one_le x
  simp only [zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

theorem exact_one_mul (x : A) : S.mul S.one x = x := by
  have h := S.one_mul_le x
  simp only [zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

theorem exact_norm_one : ‖S.one‖ = 1 := by
  have h := S.norm_one_le
  rw [abs_nonpos_iff, sub_eq_zero] at h
  exact h

theorem exact_zero_mul (x : A) : S.mul 0 x = 0 := by
  have h := S.add_mul 0 0 x
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem exact_mul_zero (x : A) : S.mul x 0 = 0 := by
  have h := S.mul_add x 0 0
  rw [add_zero] at h
  exact left_eq_add.1 h

/-- A type synonym for `A` carrying the C*-algebra structure of an exact structure `S`. -/
def Exact (_ : EpsCStar 0 A) : Type := A

instance exactNormedRing : NormedRing (Exact S) where
  __ := (inferInstance : NormedAddCommGroup A)
  mul := S.mul
  mul_assoc := exact_assoc S
  one := S.one
  one_mul := exact_one_mul S
  mul_one := exact_mul_one S
  left_distrib := S.mul_add
  right_distrib := S.add_mul
  zero_mul := exact_zero_mul S
  mul_zero := exact_mul_zero S
  norm_mul_le x y := by
    have h := S.norm_mul_le x y
    simp only [add_zero, one_mul] at h
    exact h

instance exactNormedSpace : NormedSpace ℂ (Exact S) := inferInstanceAs (NormedSpace ℂ A)

instance exactStarRing : StarRing (Exact S) where
  star := S.star
  star_involutive := S.star_star
  star_mul := S.star_mul
  star_add := S.star_add

instance exactAlgebra : Algebra ℂ (Exact S) :=
  Algebra.ofModule (fun c x y => S.smul_mul c x y) (fun c x y => S.mul_smul c x y)

instance exactNormedAlgebra : NormedAlgebra ℂ (Exact S) where
  norm_smul_le c x := norm_smul_le c x

instance exactStarModule : StarModule ℂ (Exact S) where
  star_smul c x := S.star_smul c x

instance exactCStarRing : CStarRing (Exact S) where
  norm_mul_self_le x := by
    have h := S.cstar_le x
    simp only [sub_zero, one_mul] at h
    have h' : ‖(x : A)‖ * ‖(x : A)‖ ≤ ‖S.mul (S.star x) x‖ := by rw [← sq]; exact h
    exact h'

instance exactNontrivial : Nontrivial (Exact S) :=
  ⟨⟨S.one, 0, fun h => by
    have h1 := exact_norm_one S
    have h2 : S.one = (0 : A) := h
    rw [h2, norm_zero] at h1
    exact zero_ne_one h1⟩⟩

/-- (3) At `ε = 0`, the conclusion of the assumed `KitaevFiniteDim` holds outright, for every
constant `C`: the exact structure *is* a C*-algebra and the identity is a 0-isomorphism. -/
theorem kitaev_hypothesis_exact_case (C : ℝ) [CompleteSpace A] :
    ∃ (B : Type) (_ : CStarAlgebra B) (_ : Nontrivial B),
      Nonempty (DeltaIso (C * 0) (ofCStarAlgebra B) S) := by
  let _ : CompleteSpace (Exact S) := inferInstanceAs (CompleteSpace A)
  let _ : CStarAlgebra (Exact S) := {}
  refine ⟨Exact S, inferInstance, exactNontrivial S, ⟨?_⟩⟩
  exact
    { toEquiv := LinearEquiv.refl ℂ A
      map_star := fun _ => rfl
      map_one_le := by
        change ‖(S.one : A) - S.one‖ ≤ C * 0
        simp
      map_mul_le := fun x y => by
        change ‖S.mul x y - S.mul x y‖ ≤ C * 0 * ‖(x : A)‖ * ‖(y : A)‖
        simp
      le_norm_map := fun x => by
        change (1 - C * 0) * ‖(x : A)‖ ≤ ‖(x : A)‖
        simp
      norm_map_le := fun x => by
        change ‖(x : A)‖ ≤ (1 + C * 0) * ‖(x : A)‖
        simp }

end Exact

end Cert.KitaevSectors
