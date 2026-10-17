import Certs.KitaevChannels.Upsilon

/-!
# From `‖Υ - Υ̃‖_cb ≤ Q` to the two conclusions of Theorem A, and the exact case `η = 0`

The per-block bound of `UpsBlock` carries the slack `τ > 0` of the approximate maximizer, so it
cannot give the exact bound `C·0` at `η = 0`. There a separate argument is used: at `η = δ = 0`
the map `v` is a unital complete isometry, which forces `Υ̃ = v⁻¹Φ̃` itself to be UCP.
-/

open scoped ComplexOrder InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

/-- A unital isometric linear map between C*-algebras reflects positivity of self-adjoint
elements: if `‖t - y‖ = ‖t - f(y)‖ ≤ t` for `t = ‖y‖` then `y ≥ 0`. -/
theorem nonneg_of_unital_isometry {A B : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] (f : A →ₗ[ℂ] B)
    (hiso : ∀ a, ‖f a‖ = ‖a‖) (h1 : f 1 = 1) {y : A} (hy : IsSelfAdjoint y) (hfy : 0 ≤ f y) :
    0 ≤ y := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim y 0]
  set t := ‖y‖
  have ht : 0 ≤ t := norm_nonneg _
  have eA : algebraMap ℝ A t = (t : ℂ) • 1 := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  have eB : algebraMap ℝ B t = (t : ℂ) • 1 := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  have hfn : ‖f y‖ = t := hiso y
  have hB : ‖algebraMap ℝ B t - f y‖ ≤ t := by
    have k1 : f y ≤ algebraMap ℝ B t := (CStarAlgebra.norm_le_iff_le_algebraMap (f y) ht hfy).1 hfn.le
    have k2 : 0 ≤ algebraMap ℝ B t - f y := sub_nonneg.2 k1
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ ht k2).2 (sub_le_self _ hfy)
  have hA : ‖algebraMap ℝ A t - y‖ ≤ t := by
    rw [← hiso, map_sub, eA, map_smul, h1, ← eB]
    exact hB
  have hZsa : IsSelfAdjoint (algebraMap ℝ A t - y) := (IsSelfAdjoint.algebraMap _ (.all t)).sub hy
  have hle : algebraMap ℝ A t - y ≤ algebraMap ℝ A t :=
    le_algebraMap_of_spectrum_le (fun r hr => (Real.le_norm_self r).trans
      ((spectrum.norm_le_norm_of_mem hr).trans hA)) hZsa
  exact (sub_le_self_iff _).1 hle

/-- The amplification `X ↦ (φ(Xᵢⱼ))` as a linear map. -/
def ampL {M₁ M₂ : Type*} [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
    [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂] (n : ℕ) (φ : M₁ →ₗ[ℂ] M₂) :
    Mat n M₁ →ₗ[ℂ] Mat n M₂ where
  toFun X := X.map φ
  map_add' X Y := amp_add X Y φ
  map_smul' c X := amp_smul X c φ

namespace Ctx

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
  (C : Ctx H)

theorem amp_v_star {n : ℕ} (Y : Mat n (BlockAlg C.d)) : (star Y).map C.v = star (Y.map C.v) :=
  CStarMatrix.ext fun i k => by
    rw [amp_apply, CStarMatrix.star_apply, CStarMatrix.star_apply, amp_apply, v_star C.hv]

/-- **The exact case.** If `δ = η = 0` then `Υ̃` is UCP. -/
theorem upsTilde_ucp_exact (hδ0 : C.δ = 0) (hη0 : C.η = 0) : IsUCP (upsTilde C.hv) := by
  have hiso : ∀ (n : ℕ) (Z : Mat n (BlockAlg C.d)), ‖Z.map C.v‖ = ‖Z‖ := fun n Z => by
    have h := C.hv.2.2.2.2 n Z 0
    simp only [hδ0, sub_zero, add_zero, one_mul] at h
    exact le_antisymm h.2.2 h.2.1
  have hv1 : C.v 1 = 1 := by
    have := v_one C.hv
    rw [hδ0] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hPT : ∀ x, tildePhi C.Φ x = C.Φ x := fun x => by
    have h := (tildePhi_sub_cb C.hF C.hΦ C.hcb C.hη C.hη8).apply_le x
    rw [hη0, mul_zero, zero_mul, LinearMap.sub_apply] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
  refine ⟨?_, fun n X hX => ?_⟩
  · apply C.hv.1
    rw [v_upsTilde C.hv, tilde_one C.hA, hv1]
  · set Y := X.map (upsTilde C.hv)
    have hYv : Y.map C.v = X.map C.Φ.toLinearMap := CStarMatrix.ext fun i k => by
      change C.v (upsTilde C.hv (X i k)) = C.Φ (X i k)
      rw [v_upsTilde C.hv, hPT]
    have hP : 0 ≤ X.map C.Φ.toLinearMap := C.hΦ.2 n X hX
    have hvinj : ∀ Z₁ Z₂ : Mat n (BlockAlg C.d), Z₁.map C.v = Z₂.map C.v → Z₁ = Z₂ :=
      fun Z₁ Z₂ h => by
        have := hiso n (Z₁ - Z₂)
        rw [amp_sub, h, sub_self, norm_zero] at this
        exact sub_eq_zero.1 (norm_eq_zero.1 this.symm)
    have hYsa : IsSelfAdjoint Y := by
      refine hvinj _ _ ?_
      rw [C.amp_v_star, hYv]
      exact hP.isSelfAdjoint.star_eq
    have hone : (1 : Mat n (BlockAlg C.d)).map C.v = 1 := CStarMatrix.ext fun i k => by
      rw [amp_apply, CStarMatrix.one_apply, CStarMatrix.one_apply]
      split_ifs
      · exact hv1
      · exact map_zero C.v
    refine nonneg_of_unital_isometry (ampL n C.v) (hiso n) hone hYsa ?_
    change 0 ≤ Y.map C.v
    rw [hYv]
    exact hP

/-- **Conclusion (ii) of Theorem A** from `‖Υ - Υ̃‖_cb ≤ Q`. -/
theorem final_bounds (Υ : (H →L[ℂ] H) →ₗ[ℂ] BlockAlg C.d) (hΥ : IsUCP Υ) {Q : ℝ}
    (hQ : CBBound (Υ - upsTilde C.hv) Q) (hQ0 : 0 ≤ Q) (hδ1 : C.δ < 1) :
    CBBound (C.Δ ∘ₗ Υ - C.Φ.toLinearMap) (C.e + (1 + C.δ) * Q + 12 * C.η) ∧
    ∀ (n : ℕ) (X Y : Mat n (BlockAlg C.d)),
      ‖(X.map C.Δ * Y.map C.Δ).map Υ - X * Y‖
        ≤ (Q + (12 * C.η + C.e35 + C.e) / (1 - C.δ)) * ‖X‖ * ‖Y‖ := by
  have hδ0 : 0 < 1 - C.δ := by linarith
  have hntr : Nontrivial (BlockAlg C.d) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have h1 : C.v 1 = 0 := by rw [Subsingleton.elim (1 : BlockAlg C.d) 0, map_zero]
    have h2 := v_one C.hv
    rw [h1, zero_sub, norm_neg, norm_one] at h2
    linarith
  have hΥcb : CBBound Υ 1 := cb_of_ucp C.hF hΥ
  refine ⟨?_, fun n X Y => ?_⟩
  · have e : C.Δ ∘ₗ Υ - C.Φ.toLinearMap = (C.Δ - C.v) ∘ₗ Υ + C.v ∘ₗ (Υ - upsTilde C.hv)
        + ((tildePhi C.Φ).toLinearMap - C.Φ.toLinearMap) := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_sub,
        ContinuousLinearMap.coe_coe, v_upsTilde C.hv]
      abel
    rw [e]
    have h1 := C.hΔv.comp C.he hΥcb
    have h2 := (v_cb C.hv).comp (by linarith [C.hδ]) hQ
    have h3 := tildePhi_sub_cb C.hF C.hΦ C.hcb C.hη C.hη8
    refine ((h1.add h2).add h3).mono ?_
    linarith
  · set Z := X.map C.Δ * Y.map C.Δ
    have hXn := norm_nonneg X
    have hYn := norm_nonneg Y
    have hZ : ‖Z‖ ≤ ‖X‖ * ‖Y‖ := by
      have ha : ‖X.map C.Δ‖ ≤ ‖X‖ := by simpa using C.delta_cb n X
      have hb : ‖Y.map C.Δ‖ ≤ ‖Y‖ := by simpa using C.delta_cb n Y
      exact (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) hXn)
    have hsplit : Z.map Υ - X * Y = Z.map (Υ - upsTilde C.hv) + (Z.map (upsTilde C.hv) - X * Y) := by
      rw [amp_sub_fun]; abel
    have hA : ‖Z.map (Υ - upsTilde C.hv)‖ ≤ Q * (‖X‖ * ‖Y‖) :=
      (hQ n Z).trans (mul_le_mul_of_nonneg_left hZ hQ0)
    have hB : ‖Z.map (upsTilde C.hv) - X * Y‖ ≤ (12 * C.η + C.e35 + C.e) / (1 - C.δ) * (‖X‖ * ‖Y‖) := by
      have hlow := v_lower C.hv (Z.map (upsTilde C.hv) - X * Y)
      have hvZ : (Z.map (upsTilde C.hv)).map C.v = Z.map (tildePhi C.Φ).toLinearMap :=
        CStarMatrix.ext fun i k => v_upsTilde C.hv (Z i k)
      rw [amp_sub, hvZ] at hlow
      have k1 : ‖Z.map (tildePhi C.Φ).toLinearMap - Z.map C.Φ.toLinearMap‖ ≤ 12 * C.η * ‖Z‖ := by
        rw [norm_sub_rev]; exact C.phi_tilde_close Z
      have k2 : ‖Z.map C.Φ.toLinearMap - (X * Y).map C.Δ‖ ≤ C.e35 * ‖X‖ * ‖Y‖ := C.mul35 X Y
      have k3 : ‖(X * Y).map C.Δ - (X * Y).map C.v‖ ≤ C.e * ‖X * Y‖ := by
        have := C.hΔv n (X * Y); rwa [amp_sub_fun] at this
      have k4 : ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := norm_mul_le _ _
      have k5 : ‖Z.map (tildePhi C.Φ).toLinearMap - (X * Y).map C.v‖
          ≤ (12 * C.η + C.e35 + C.e) * (‖X‖ * ‖Y‖) := by
        have t1 := norm_sub_le_norm_sub_add_norm_sub (Z.map (tildePhi C.Φ).toLinearMap)
          (Z.map C.Φ.toLinearMap) ((X * Y).map C.v)
        have t2 := norm_sub_le_norm_sub_add_norm_sub (Z.map C.Φ.toLinearMap)
          ((X * Y).map C.Δ) ((X * Y).map C.v)
        have := C.hη; have := C.he; have := C.e35_nonneg
        have := mul_le_mul_of_nonneg_left hZ (by positivity : (0 : ℝ) ≤ 12 * C.η)
        have := mul_le_mul_of_nonneg_left k4 C.he
        nlinarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
      nlinarith
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := add_le_add hA hB
    linarith

end Ctx

end Cert.KitaevChannels
