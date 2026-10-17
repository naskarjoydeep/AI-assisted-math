import LeanProof.Defs
import Mathlib.Analysis.CStarAlgebra.lpSpace

/-!
# ℓ^∞-direct sums: infinitely many finite sectors

* `lpEpsCStar S` : the ℓ^∞-direct sum of a family of ε-C* algebras is an ε-C* algebra.
* `lpDeltaIso`   : a family of δ-isomorphisms `B i → A i` from C*-algebras (same δ < 1)
  assembles into a δ-isomorphism `ℓ^∞(B) → ℓ^∞(A)`.
* `sectors_of_kitaev` : *assuming* Kitaev's finite-dimensional theorem (as the explicit
  hypothesis `KitaevFiniteDim C ε₀`), every ℓ^∞-direct sum of finite-dimensional ε-C* algebras,
  infinite-dimensional as it may be, is `(C ε)`-isomorphic to a C*-algebra.
-/

open scoped ENNReal ComplexConjugate

noncomputable section

namespace Kitaev

variable {ι : Type*} {A : ι → Type*} [∀ i, NormedAddCommGroup (A i)] [∀ i, NormedSpace ℂ (A i)]

theorem norm_coord_le {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] (f : lp E ∞) (i : ι) :
    ‖f i‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero f i

section Sum

variable {ε : ℝ} (S : ∀ i, EpsCStar ε (A i))

/-- coordinatewise product on `ℓ^∞(A)` -/
def lpMul (hε : 0 ≤ ε) (f g : lp A ∞) : lp A ∞ :=
  ⟨fun i => (S i).mul (f i) (g i), memℓp_infty ⟨(1 + ε) * ‖f‖ * ‖g‖, by
    rintro _ ⟨i, rfl⟩
    calc ‖(S i).mul (f i) (g i)‖ ≤ (1 + ε) * ‖f i‖ * ‖g i‖ := (S i).norm_mul_le _ _
      _ ≤ (1 + ε) * ‖f‖ * ‖g‖ := by
          have := norm_coord_le f i
          have := norm_coord_le g i
          gcongr⟩⟩

/-- coordinatewise involution on `ℓ^∞(A)` -/
def lpStar (f : lp A ∞) : lp A ∞ :=
  ⟨fun i => (S i).star (f i), memℓp_infty ⟨‖f‖, by
    rintro _ ⟨i, rfl⟩
    simp only [(S i).norm_star]
    exact norm_coord_le f i⟩⟩

/-- coordinatewise unit of `ℓ^∞(A)` -/
def lpOne : lp A ∞ :=
  ⟨fun i => (S i).one, memℓp_infty ⟨1 + ε, by
    rintro _ ⟨i, rfl⟩
    have := (abs_le.1 (S i).norm_one_le).2
    simp only
    linarith⟩⟩

@[simp] theorem lpMul_apply (hε : 0 ≤ ε) (f g : lp A ∞) (i : ι) :
    lpMul S hε f g i = (S i).mul (f i) (g i) := rfl

@[simp] theorem lpStar_apply (f : lp A ∞) (i : ι) : lpStar S f i = (S i).star (f i) := rfl

@[simp] theorem lpOne_apply (i : ι) : lpOne S i = (S i).one := rfl

/-- **The ℓ^∞-direct sum of ε-C* algebras is an ε-C* algebra.**
`Nonempty ι` is needed for the unit-norm axiom `|‖I‖ - 1| ≤ ε`. -/
def lpEpsCStar [Nonempty ι] (hε : 0 ≤ ε) : EpsCStar ε (lp A ∞) where
  mul := lpMul S hε
  mul_add f g h := lp.ext <| funext fun i => by simp [(S i).mul_add]
  add_mul f g h := lp.ext <| funext fun i => by simp [(S i).add_mul]
  mul_smul c f g := lp.ext <| funext fun i => by simp [(S i).mul_smul]
  smul_mul c f g := lp.ext <| funext fun i => by simp [(S i).smul_mul]
  star := lpStar S
  star_add f g := lp.ext <| funext fun i => by simp [(S i).star_add]
  star_smul c f := lp.ext <| funext fun i => by simp [(S i).star_smul]
  star_star f := lp.ext <| funext fun i => by simp [(S i).star_star]
  norm_star f := by
    apply le_antisymm
    · refine lp.norm_le_of_forall_le (norm_nonneg f) fun i => ?_
      simpa [(S i).norm_star] using norm_coord_le f i
    · refine lp.norm_le_of_forall_le (norm_nonneg _) fun i => ?_
      have := norm_coord_le (lpStar S f) i
      simpa [(S i).norm_star] using this
  star_mul f g := lp.ext <| funext fun i => by simp [(S i).star_mul]
  one := lpOne S
  star_one := lp.ext <| funext fun i => by simp [(S i).star_one]
  norm_mul_le f g := by
    refine lp.norm_le_of_forall_le (by positivity) fun i => ?_
    calc ‖lpMul S hε f g i‖ ≤ (1 + ε) * ‖f i‖ * ‖g i‖ := (S i).norm_mul_le _ _
      _ ≤ (1 + ε) * ‖f‖ * ‖g‖ := by
          have := norm_coord_le f i
          have := norm_coord_le g i
          gcongr
  assoc_le f g h := by
    refine lp.norm_le_of_forall_le (by positivity) fun i => ?_
    calc ‖(lpMul S hε (lpMul S hε f g) h - lpMul S hε f (lpMul S hε g h)) i‖
        = ‖(S i).mul ((S i).mul (f i) (g i)) (h i) - (S i).mul (f i) ((S i).mul (g i) (h i))‖ :=
          rfl
      _ ≤ ε * ‖f i‖ * ‖g i‖ * ‖h i‖ := (S i).assoc_le _ _ _
      _ ≤ ε * ‖f‖ * ‖g‖ * ‖h‖ := by
          have := norm_coord_le f i
          have := norm_coord_le g i
          have := norm_coord_le h i
          gcongr
  cstar_le f := by
    set N := ‖lpMul S hε (lpStar S f) f‖ with hN
    by_cases hε1 : 1 - ε ≤ 0
    · have : (1 - ε) * ‖f‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hε1 (sq_nonneg _)
      exact this.trans (norm_nonneg _)
    · push Not at hε1
      have hcoord : ∀ i, ‖f i‖ ≤ Real.sqrt (N / (1 - ε)) := by
        intro i
        apply Real.le_sqrt_of_sq_le
        rw [le_div_iff₀ hε1]
        calc ‖f i‖ ^ 2 * (1 - ε) = (1 - ε) * ‖f i‖ ^ 2 := by ring
          _ ≤ ‖(S i).mul ((S i).star (f i)) (f i)‖ := (S i).cstar_le _
          _ = ‖lpMul S hε (lpStar S f) f i‖ := rfl
          _ ≤ N := norm_coord_le _ i
      have hf : ‖f‖ ≤ Real.sqrt (N / (1 - ε)) :=
        lp.norm_le_of_forall_le (Real.sqrt_nonneg _) hcoord
      have hf2 : ‖f‖ ^ 2 ≤ N / (1 - ε) := by
        calc ‖f‖ ^ 2 ≤ Real.sqrt (N / (1 - ε)) ^ 2 := by gcongr
          _ = N / (1 - ε) := Real.sq_sqrt (div_nonneg (norm_nonneg _) hε1.le)
      rw [le_div_iff₀ hε1] at hf2
      linarith
  mul_one_le f := by
    refine lp.norm_le_of_forall_le (by positivity) fun i => ?_
    calc ‖(lpMul S hε f (lpOne S) - f) i‖ = ‖(S i).mul (f i) (S i).one - f i‖ := rfl
      _ ≤ ε * ‖f i‖ := (S i).mul_one_le _
      _ ≤ ε * ‖f‖ := by have := norm_coord_le f i; gcongr
  one_mul_le f := by
    refine lp.norm_le_of_forall_le (by positivity) fun i => ?_
    calc ‖(lpMul S hε (lpOne S) f - f) i‖ = ‖(S i).mul (S i).one (f i) - f i‖ := rfl
      _ ≤ ε * ‖f i‖ := (S i).one_mul_le _
      _ ≤ ε * ‖f‖ := by have := norm_coord_le f i; gcongr
  norm_one_le := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    rw [abs_le]
    constructor
    · have h1 := (abs_le.1 (S i₀).norm_one_le).1
      have h2 := norm_coord_le (lpOne S) i₀
      simp only [lpOne_apply] at h2
      linarith
    · have : ‖lpOne S‖ ≤ 1 + ε := by
        refine lp.norm_le_of_forall_le (by linarith) fun i => ?_
        have := (abs_le.1 (S i).norm_one_le).2
        simp only [lpOne_apply]
        linarith
      linarith

/-- The ℓ^∞-direct sum of Banach spaces is a Banach space. -/
example [∀ i, CompleteSpace (A i)] : CompleteSpace (lp A ∞) := inferInstance

end Sum

section Iso

variable {B : ι → Type*} [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)]

instance lpCStarAlgebra : CStarAlgebra (lp B ∞) where

instance lpNontrivial [Nonempty ι] : Nontrivial (lp B ∞) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrFun (congrArg (fun f : lp B ∞ => (f : ∀ i, B i)) h) i₀
  simp at this

variable {ε δ : ℝ} (S : ∀ i, EpsCStar ε (A i))

/-- the coordinatewise linear bijection `ℓ^∞(B) ≃ ℓ^∞(A)` -/
def lpEquiv (hδ0 : 0 ≤ δ) (hδ : δ < 1) (v : ∀ i, DeltaIso δ (ofCStarAlgebra (B i)) (S i)) :
    lp B ∞ ≃ₗ[ℂ] lp A ∞ where
  toFun f := ⟨fun i => (v i).toEquiv (f i), memℓp_infty ⟨(1 + δ) * ‖f‖, by
    rintro _ ⟨i, rfl⟩
    calc ‖(v i).toEquiv (f i)‖ ≤ (1 + δ) * ‖f i‖ := (v i).norm_map_le _
      _ ≤ (1 + δ) * ‖f‖ := by have := norm_coord_le f i; gcongr⟩⟩
  invFun g := ⟨fun i => (v i).toEquiv.symm (g i), memℓp_infty ⟨‖g‖ / (1 - δ), by
    rintro _ ⟨i, rfl⟩
    have h1 : 0 < 1 - δ := by linarith
    have hl := (v i).le_norm_map ((v i).toEquiv.symm (g i))
    rw [LinearEquiv.apply_symm_apply] at hl
    have := norm_coord_le g i
    simp only
    rw [le_div_iff₀ h1]
    linarith⟩⟩
  map_add' f g := lp.ext <| funext fun i => by
    change (v i).toEquiv (f i + g i) = (v i).toEquiv (f i) + (v i).toEquiv (g i)
    exact map_add _ _ _
  map_smul' c f := lp.ext <| funext fun i => by
    change (v i).toEquiv (c • f i) = c • (v i).toEquiv (f i)
    exact map_smul _ _ _
  left_inv f := lp.ext <| funext fun i => by simp
  right_inv g := lp.ext <| funext fun i => by simp

@[simp] theorem lpEquiv_apply (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (v : ∀ i, DeltaIso δ (ofCStarAlgebra (B i)) (S i)) (f : lp B ∞) (i : ι) :
    lpEquiv S hδ0 hδ v f i = (v i).toEquiv (f i) := rfl

/-- **Sector theorem.** Coordinatewise δ-isomorphisms from C*-algebras (with a common δ < 1)
assemble into a δ-isomorphism from the C*-algebra `ℓ^∞(B)` onto the ε-C* algebra `ℓ^∞(A)`. -/
def lpDeltaIso [Nonempty ι] (hε : 0 ≤ ε) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (v : ∀ i, DeltaIso δ (ofCStarAlgebra (B i)) (S i)) :
    DeltaIso δ (ofCStarAlgebra (lp B ∞)) (lpEpsCStar S hε) where
  toEquiv := lpEquiv S hδ0 hδ v
  map_star f := lp.ext <| funext fun i => by
    have := (v i).map_star (f i)
    simpa [ofCStarAlgebra, lpEpsCStar] using this
  map_one_le := by
    refine lp.norm_le_of_forall_le hδ0 fun i => ?_
    have := (v i).map_one_le
    simpa [ofCStarAlgebra, lpEpsCStar] using this
  map_mul_le f g := by
    refine lp.norm_le_of_forall_le (by positivity) fun i => ?_
    calc ‖(lpEquiv S hδ0 hδ v (f * g) - lpMul S hε (lpEquiv S hδ0 hδ v f) (lpEquiv S hδ0 hδ v g)) i‖
        = ‖(v i).toEquiv (f i * g i) - (S i).mul ((v i).toEquiv (f i)) ((v i).toEquiv (g i))‖ :=
          rfl
      _ ≤ δ * ‖f i‖ * ‖g i‖ := (v i).map_mul_le (f i) (g i)
      _ ≤ δ * ‖f‖ * ‖g‖ := by
          have := norm_coord_le f i
          have := norm_coord_le g i
          gcongr
  le_norm_map f := by
    by_cases hδ1 : 1 - δ ≤ 0
    · exact (mul_nonpos_of_nonpos_of_nonneg hδ1 (norm_nonneg _)).trans (norm_nonneg _)
    · push Not at hδ1
      have hf : ‖f‖ ≤ ‖lpEquiv S hδ0 hδ v f‖ / (1 - δ) := by
        refine lp.norm_le_of_forall_le (div_nonneg (norm_nonneg _) hδ1.le) fun i => ?_
        rw [le_div_iff₀ hδ1]
        have h1 := (v i).le_norm_map (f i)
        have h2 := norm_coord_le (lpEquiv S hδ0 hδ v f) i
        simp only [lpEquiv_apply] at h2
        linarith
      rw [le_div_iff₀ hδ1] at hf
      change (1 - δ) * ‖f‖ ≤ ‖lpEquiv S hδ0 hδ v f‖
      linarith
  norm_map_le f := by
    refine lp.norm_le_of_forall_le (by positivity) fun i => ?_
    calc ‖lpEquiv S hδ0 hδ v f i‖ = ‖(v i).toEquiv (f i)‖ := rfl
      _ ≤ (1 + δ) * ‖f i‖ := (v i).norm_map_le _
      _ ≤ (1 + δ) * ‖f‖ := by have := norm_coord_le f i; gcongr

end Iso

/-- **Theorem B (sectors), from Kitaev's finite-dimensional theorem.**
If Kitaev's Theorem 2.3 holds with constants `C, ε₀` (hypothesis `hK`), then every ℓ^∞-direct
sum of finite-dimensional ε-C* algebras (`0 ≤ ε < ε₀`, `C ε < 1`) — an infinite-dimensional
ε-C* algebra in general — admits a `(C ε)`-isomorphism, in particular a linear bijection,
from a genuine C*-algebra. -/
theorem sectors_of_kitaev {C ε₀ : ℝ} (hK : KitaevFiniteDim C ε₀) (hC : 0 ≤ C)
    {ε : ℝ} (hε : 0 ≤ ε) (hε₀ : ε < ε₀) (hCε : C * ε < 1)
    {ι : Type} [Nonempty ι] {A : ι → Type} [∀ i, NormedAddCommGroup (A i)]
    [∀ i, NormedSpace ℂ (A i)] [∀ i, CompleteSpace (A i)] [∀ i, FiniteDimensional ℂ (A i)]
    (S : ∀ i, EpsCStar ε (A i)) :
    ∃ (B : Type) (_ : CStarAlgebra B) (_ : Nontrivial B),
      Nonempty (DeltaIso (C * ε) (ofCStarAlgebra B) (lpEpsCStar S hε)) := by
  have h := fun i => hK (A i) ε (S i) hε hε₀
  choose B instB ntB v using h
  let _ : ∀ i, CStarAlgebra (B i) := instB
  let _ : ∀ i, Nontrivial (B i) := ntB
  exact ⟨lp B ∞, inferInstance, inferInstance,
    ⟨lpDeltaIso S hε (mul_nonneg hC hε) hCε (fun i => (v i).some)⟩⟩

end Kitaev
