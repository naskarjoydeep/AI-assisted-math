import Certs.KitaevChannels.Objects
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Normalization `x ↦ c φ(x) c` with `c = φ(1)^{-1/2}`

Kitaev normalizes `Δ'` and `Υ'` by `Δ'(I)^{-1/2}` and `Υ'(1)^{-1/2}`. We prove: for a self-adjoint
`a` with `‖a - 1‖ ≤ t ≤ 1/2` there is a self-adjoint `c` with `c a c = 1` and `‖c - 1‖ ≤ 2t`;
and two-sided multiplications are completely bounded by `‖a‖ ‖b‖`.
-/

open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

section LR

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

theorem lrMul_cb (a b : M) : CBBound (lrMul a b) (‖a‖ * ‖b‖) := fun n X => by
  rw [amp_lrMul]
  calc ‖diagM n a * X * diagM n b‖ ≤ ‖diagM n a‖ * ‖X‖ * ‖diagM n b‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr; exact norm_mul_le _ _
    _ ≤ ‖a‖ * ‖X‖ * ‖b‖ := by
        gcongr
        · exact norm_diagM_le n a
        · exact norm_diagM_le n b
    _ = ‖a‖ * ‖b‖ * ‖X‖ := by ring

end LR

section Inv

/-- For `x ∈ [1-t, 1+t]` with `t ≤ 1/2`: `|1/√x - 1| ≤ 2t`. -/
theorem inv_sqrt_sub_one_le {x t : ℝ} (ht : t ≤ 1 / 2) (hx : |x - 1| ≤ t) :
    |(Real.sqrt x)⁻¹ - 1| ≤ 2 * t := by
  have hx0 : 1 / 2 ≤ x := by have := (abs_le.1 hx).1; linarith
  set r := Real.sqrt x with hr
  have hr2 : r ^ 2 = x := Real.sq_sqrt (by linarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg x
  have hrh : 1 / 2 ≤ r := by nlinarith
  have hrpos : 0 < r := by linarith
  have h1 : |1 - r| * (1 + r) = |x - 1| := by
    rw [← hr2, show r ^ 2 - 1 = -((1 - r) * (1 + r)) by ring, abs_neg, abs_mul,
      abs_of_pos (by linarith : (0 : ℝ) < 1 + r)]
  have h2 : |1 - r| ≤ t := by
    have : |1 - r| * (1 + r) ≤ t := h1 ▸ hx
    nlinarith [abs_nonneg (1 - r)]
  rw [show r⁻¹ - 1 = (1 - r) / r by field_simp, abs_div, abs_of_pos hrpos, div_le_iff₀ hrpos]
  nlinarith [abs_nonneg (1 - r)]

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- `c = a^{-1/2}`: `c` self-adjoint, `c a c = 1`, `‖c - 1‖ ≤ 2 ‖a - 1‖` when `‖a - 1‖ ≤ 1/2`. -/
theorem exists_normalizer [Nontrivial M] {a : M} (ha : IsSelfAdjoint a) {t : ℝ}
    (hat : ‖a - 1‖ ≤ t) (ht : t ≤ 1 / 2) :
    ∃ c : M, IsSelfAdjoint c ∧ c * a * c = 1 ∧ ‖c - 1‖ ≤ 2 * t := by
  have hspec : ∀ x ∈ spectrum ℝ a, |x - 1| ≤ t := fun x hx => by
    have h1 : x - 1 ∈ spectrum ℝ (a - algebraMap ℝ M 1) := by
      rw [← spectrum.sub_singleton_eq]
      exact Set.sub_mem_sub hx rfl
    rw [map_one] at h1
    have := spectrum.norm_le_norm_of_mem h1
    rw [Real.norm_eq_abs] at this
    exact this.trans hat
  have hpos : ∀ x ∈ spectrum ℝ a, 0 < x := fun x hx => by
    have := abs_le.1 (hspec x hx); linarith
  have hcont : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ a) :=
    ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn
      (fun x hx => (Real.sqrt_pos.2 (hpos x hx)).ne')
  have ht0 : 0 ≤ t := (norm_nonneg _).trans hat
  refine ⟨cfc (fun x : ℝ => (Real.sqrt x)⁻¹) a, cfc_predicate _ a, ?_, ?_⟩
  · have e1 : cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) a
        = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) a * a * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) a := by
      rw [cfc_mul (fun x : ℝ => (Real.sqrt x)⁻¹ * x) (fun x : ℝ => (Real.sqrt x)⁻¹) a
          (hcont.mul continuousOn_id) hcont,
        cfc_mul (fun x : ℝ => (Real.sqrt x)⁻¹) (fun x : ℝ => x) a hcont continuousOn_id,
        cfc_id' ℝ a]
    rw [← e1, ← cfc_const_one ℝ a]
    refine cfc_congr fun x hx => ?_
    have hx0 := hpos x hx
    have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hsp : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    field_simp
    linarith
  · have e2 : cfc (fun x : ℝ => (Real.sqrt x)⁻¹) a - 1 = cfc (fun x : ℝ => (Real.sqrt x)⁻¹ - 1) a := by
      rw [cfc_sub (fun x : ℝ => (Real.sqrt x)⁻¹) (fun _ : ℝ => (1 : ℝ)) a hcont continuousOn_const,
        cfc_const_one ℝ a]
    rw [e2]
    exact norm_cfc_le (by linarith) fun x hx => by
      rw [Real.norm_eq_abs]; exact inv_sqrt_sub_one_le ht (hspec x hx)

end Inv

end Cert.KitaevChannels
