import Certs.KitaevChannels.Tilde

/-!
# Kitaev's `Δ̃ = v` and `Υ̃ = v⁻¹ Φ̃` (equations (12.25)–(12.27))

From Theorem 12.1 (the algebra `A = Im Φ̃` with `X ⋆ Y = Φ̃(XY)`) and Theorem 10.5 (an extended
δ-isomorphism `v : B → A`), we build `Υ̃ : B(H) → B` and record every property used later.
-/

open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem matMul_choiEffros (Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) {n : ℕ} (P Q : Mat n (H →L[ℂ] H)) :
    matMul (choiEffros Φ) P Q = (P * Q).map (tildePhi Φ).toLinearMap := by
  refine CStarMatrix.ext fun i j => ?_
  change ∑ l, tildePhi Φ (P i l * Q l j) = tildePhi Φ (∑ l, P i l * Q l j)
  rw [map_sum]

section Fix

variable {Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)} {ε : ℝ}

/-- `Φ̃` is the identity on `A = Im Φ̃` (from the exact unit `X ⋆ I = X`). -/
theorem tilde_fix (hA : ExtEpsCStarSub ε (LinearMap.range (tildePhi Φ).toLinearMap) (choiEffros Φ))
    {x : H →L[ℂ] H} (hx : x ∈ LinearMap.range (tildePhi Φ).toLinearMap) : tildePhi Φ x = x := by
  have h := (hA.2.2.2.2.1 x hx).1
  simpa [choiEffros] using h

theorem tilde_one (hA : ExtEpsCStarSub ε (LinearMap.range (tildePhi Φ).toLinearMap) (choiEffros Φ)) :
    tildePhi Φ 1 = 1 := tilde_fix hA hA.1

end Fix

section Ups

variable {Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)} {m : ℕ} {d : Fin m → ℕ}
  {v : BlockAlg d →ₗ[ℂ] (H →L[ℂ] H)} {δ : ℝ}

/-- `Υ̃ = v⁻¹ ∘ Φ̃`. -/
def upsTilde (hv : IsExtDeltaIsoOnto δ (LinearMap.range (tildePhi Φ).toLinearMap) (choiEffros Φ) v) :
    (H →L[ℂ] H) →ₗ[ℂ] BlockAlg d :=
  (LinearEquiv.ofInjective v hv.1).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range v) (tildePhi Φ).toLinearMap
      (fun x => by rw [hv.2.1]; exact LinearMap.mem_range_self _ x)

variable (hv : IsExtDeltaIsoOnto δ (LinearMap.range (tildePhi Φ).toLinearMap) (choiEffros Φ) v)
include hv

/-- (12.25) `Δ̃ Υ̃ = Φ̃`. -/
theorem v_upsTilde (x : H →L[ℂ] H) : v (upsTilde hv x) = tildePhi Φ x := by
  have := LinearEquiv.ofInjective_apply v (h := hv.1)
    ((LinearEquiv.ofInjective v hv.1).symm ⟨tildePhi Φ x, by rw [hv.2.1]; exact LinearMap.mem_range_self _ x⟩)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem v_mem (b : BlockAlg d) : v b ∈ LinearMap.range (tildePhi Φ).toLinearMap := by
  rw [← hv.2.1]; exact LinearMap.mem_range_self v b

/-- (12.25) `Υ̃ Δ̃ = 1`. -/
theorem upsTilde_v {ε : ℝ}
    (hA : ExtEpsCStarSub ε (LinearMap.range (tildePhi Φ).toLinearMap) (choiEffros Φ))
    (b : BlockAlg d) : upsTilde hv (v b) = b := by
  apply hv.1
  rw [v_upsTilde hv, tilde_fix hA (v_mem hv b)]

/-- (12.26) `‖Δ̃(I) - 1‖ ≤ δ`. -/
theorem v_one : ‖v 1 - 1‖ ≤ δ := hv.2.2.2.1

theorem v_star (b : BlockAlg d) : v (star b) = star (v b) := hv.2.2.1 b

theorem v_cb : CBBound v (1 + δ) := fun n X => (hv.2.2.2.2 n X 0).2.2

theorem v_lower {n : ℕ} (X : Mat n (BlockAlg d)) : (1 - δ) * ‖X‖ ≤ ‖X.map v‖ :=
  (hv.2.2.2.2 n X 0).2.1

/-- (12.27) `‖Φ̃ₙ(Δ̃ₙ(X) Δ̃ₙ(Y)) - Δ̃ₙ(XY)‖ ≤ δ ‖X‖ ‖Y‖`. -/
theorem v_mul {n : ℕ} (X Y : Mat n (BlockAlg d)) :
    ‖(X.map v * Y.map v).map (tildePhi Φ).toLinearMap - (X * Y).map v‖ ≤ δ * ‖X‖ * ‖Y‖ := by
  have h := (hv.2.2.2.2 n X Y).1
  rw [matMul_choiEffros, norm_sub_rev] at h
  exact h

theorem upsTilde_cb (hF : CPMapFacts) [Nontrivial H] {η : ℝ} (hΦ : IsUCP Φ.toLinearMap)
    (hcb : CBBound (Φ * Φ - Φ).toLinearMap η) (hη : 0 ≤ η) (hη8 : η ≤ 1 / 8) (hδ : δ < 1) :
    CBBound (upsTilde hv) ((1 + 12 * η) / (1 - δ)) := fun n X => by
  have h1 : 0 < 1 - δ := by linarith
  have hT : CBBound (tildePhi Φ).toLinearMap (1 + 12 * η) := by
    have := (cb_of_ucp hF hΦ).add (tildePhi_sub_cb hF hΦ hcb hη hη8)
    simpa using this
  have hlow := v_lower hv (X.map (upsTilde hv))
  have e : (X.map (upsTilde hv)).map v = X.map (tildePhi Φ).toLinearMap := by
    exact CStarMatrix.ext fun i j => v_upsTilde hv (X i j)
  rw [e] at hlow
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  calc ‖X.map (upsTilde hv)‖ * (1 - δ) = (1 - δ) * ‖X.map (upsTilde hv)‖ := by ring
    _ ≤ ‖X.map (tildePhi Φ).toLinearMap‖ := hlow
    _ ≤ (1 + 12 * η) * ‖X‖ := hT n X

end Ups

end Cert.KitaevChannels
