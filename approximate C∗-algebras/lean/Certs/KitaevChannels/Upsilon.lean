import Certs.KitaevChannels.UpsBlock

/-!
# The UCP map `Υ` with `‖Υ - Υ̃‖_cb = O(η)`

`Υ' = (Υ'_1, …, Υ'_m)`, the chain `Υ' ≈ Υ'Φ ≈ Υ'Φ̃ = Υ'Δ̃Υ̃ ≈ Υ'ΔΥ̃ ≈ Υ̃`, and the normalization
`Υ = Υ'(1)^{-1/2} Υ'(·) Υ'(1)^{-1/2}` (Kitaev, end of §12.2).
-/

open scoped ComplexOrder InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

section Assemble

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
  (C : Ctx H)
  {K' : Type} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  (π : (H →L[ℂ] H) →⋆ₐ[ℂ] (K' →L[ℂ] K'))
  (L : (j : Fin C.m) → EuclideanSpace ℂ (Fin (C.d j)) →L[ℂ] K')

/-- Kitaev's `Υ' = (L_j† π(Φ(·)) L_j)_j`. -/
def upsPrime : (H →L[ℂ] H) →ₗ[ℂ] BlockAlg C.d :=
  LinearMap.pi fun j => toMat (compress π (L j) (L j) ∘ₗ C.Φ.toLinearMap)

theorem proj_upsPrime (j : Fin C.m) : LinearMap.proj j ∘ₗ upsPrime C π L
    = toMat (compress π (L j) (L j) ∘ₗ C.Φ.toLinearMap) := LinearMap.proj_pi _ _

theorem upsPrime_cp (hS : StinespringThm) : IsCP (upsPrime C π L) :=
  IsCP.of_blocks _ fun j => by
    rw [proj_upsPrime]; exact toMat_cp ((compress_cp hS π (L j)).comp C.hΦ.2)

variable (hL : ∀ j, ‖L j‖ ≤ 1)
include hL

theorem upsPrime_cb (hS : StinespringThm) : CBBound (upsPrime C π L) 1 :=
  CBBound.of_blocks _ zero_le_one fun j => by
    rw [proj_upsPrime]
    have h := (compress_cb_self C.hF hS π (L j)).comp (sq_nonneg _) C.phi_cb
    refine (toMat_cb h).mono ?_
    have := hL j; have := norm_nonneg (L j); nlinarith

theorem upsPrime_idem (hS : StinespringThm) :
    CBBound (upsPrime C π L - upsPrime C π L ∘ₗ C.Φ.toLinearMap) C.η :=
  CBBound.of_blocks _ C.hη fun j => by
    rw [LinearMap.comp_sub, ← LinearMap.comp_assoc, proj_upsPrime]
    have e : toMat (compress π (L j) (L j) ∘ₗ C.Φ.toLinearMap)
        - toMat (compress π (L j) (L j) ∘ₗ C.Φ.toLinearMap) ∘ₗ C.Φ.toLinearMap
        = toMat (compress π (L j) (L j) ∘ₗ
          (C.Φ.toLinearMap - C.Φ.toLinearMap ∘ₗ C.Φ.toLinearMap)) := by
      simp only [toMat, LinearMap.comp_sub, LinearMap.comp_assoc]
    rw [e]
    have hΦ2 : CBBound (C.Φ.toLinearMap - C.Φ.toLinearMap ∘ₗ C.Φ.toLinearMap) C.η := fun n X => by
      have h := C.hcb n X
      have e2 : X.map (C.Φ * C.Φ - C.Φ).toLinearMap
          = X.map (C.Φ.toLinearMap ∘ₗ C.Φ.toLinearMap - C.Φ.toLinearMap) := rfl
      rw [e2, amp_sub_fun, norm_sub_rev, ← amp_sub_fun] at h
      exact h
    have h := (compress_cb_self C.hF hS π (L j)).comp (sq_nonneg _) hΦ2
    refine (toMat_cb h).mono ?_
    have h1 : ‖L j‖ ^ 2 ≤ 1 := by have := hL j; have := norm_nonneg (L j); nlinarith
    have := mul_le_mul_of_nonneg_right h1 C.hη
    linarith

/-- **The chain** `Υ' ≈ Υ̃`, given the per-block bound `‖Υ'_j Δ - (·)_j‖_cb ≤ κ`. -/
theorem upsPrime_close (hS : StinespringThm) (hδ1 : C.δ < 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (hLb : ∀ j, CBBound (toMat (compress π (L j) (L j) ∘ₗ C.Φ.toLinearMap) ∘ₗ C.Δ
      - LinearMap.proj j) κ) :
    CBBound (upsPrime C π L - upsTilde C.hv)
      (C.η + 12 * C.η + C.e * ((1 + 12 * C.η) / (1 - C.δ))
        + κ * ((1 + 12 * C.η) / (1 - C.δ))) := by
  have hD : CBBound (upsPrime C π L ∘ₗ C.Δ - LinearMap.id) κ :=
    CBBound.of_blocks _ hκ fun j => by
      rw [LinearMap.comp_sub, ← LinearMap.comp_assoc, proj_upsPrime, LinearMap.comp_id]
      exact hLb j
  have e : upsPrime C π L - upsTilde C.hv
      = (upsPrime C π L - upsPrime C π L ∘ₗ C.Φ.toLinearMap)
        + upsPrime C π L ∘ₗ (C.Φ.toLinearMap - (tildePhi C.Φ).toLinearMap)
        + upsPrime C π L ∘ₗ ((C.v - C.Δ) ∘ₗ upsTilde C.hv)
        + (upsPrime C π L ∘ₗ C.Δ - LinearMap.id) ∘ₗ upsTilde C.hv := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      map_sub, ContinuousLinearMap.coe_coe, v_upsTilde C.hv]
    abel
  rw [e]
  have hu := upsTilde_cb C.hv C.hF C.hΦ C.hcb C.hη C.hη8 hδ1
  have hu0 : 0 ≤ (1 + 12 * C.η) / (1 - C.δ) := div_nonneg (by linarith [C.hη]) (by linarith)
  have hPT : CBBound (C.Φ.toLinearMap - (tildePhi C.Φ).toLinearMap) (12 * C.η) := fun n X => by
    rw [amp_sub_fun]; exact C.phi_tilde_close X
  have hvD : CBBound (C.v - C.Δ) C.e := fun n X => by
    rw [amp_sub_fun, norm_sub_rev, ← amp_sub_fun]; exact C.hΔv n X
  have hU := upsPrime_cb C π L hL hS
  have h1 := upsPrime_idem C π L hL hS
  have h2 := hU.comp zero_le_one hPT
  have h3 := hU.comp zero_le_one (hvD.comp C.he hu)
  have h4 := hD.comp hκ hu
  refine (((h1.add h2).add h3).add h4).mono ?_
  linarith

/-- **Normalization**: a UCP `Υ` with `‖Υ - Υ̃‖_cb ≤ 2t(2+2t) + q`, `t = q + δ/(1-δ) ≤ 1/2`. -/
theorem exists_Ups (hS : StinespringThm) (hδ1 : C.δ < 1) {q : ℝ}
    (hq : CBBound (upsPrime C π L - upsTilde C.hv) q)
    (hsmall : q + C.δ / (1 - C.δ) ≤ 1 / 2) :
    ∃ Υ : (H →L[ℂ] H) →ₗ[ℂ] BlockAlg C.d, IsUCP Υ ∧
      CBBound (Υ - upsTilde C.hv)
        (2 * (q + C.δ / (1 - C.δ)) * (2 + 2 * (q + C.δ / (1 - C.δ))) + q) := by
  have hδ0 : 0 < 1 - C.δ := by linarith
  have hntr : Nontrivial (BlockAlg C.d) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have h1 : C.v 1 = 0 := by rw [Subsingleton.elim (1 : BlockAlg C.d) 0, map_zero]
    have h2 := v_one C.hv
    rw [h1, zero_sub, norm_neg, norm_one] at h2
    linarith
  set t := q + C.δ / (1 - C.δ)
  set a := upsPrime C π L 1
  have hcp := upsPrime_cp C π L hS
  have hsa : IsSelfAdjoint a := by
    have := star_of_cp C.hF hcp 1
    rw [star_one] at this
    exact this.symm
  have hq0 : 0 ≤ q := by
    have := hq 1 (diagM 1 1)
    have h0 := norm_nonneg ((diagM 1 (1 : H →L[ℂ] H)).map (upsPrime C π L - upsTilde C.hv))
    rw [norm_diagM_one, norm_one] at this
    linarith
  have hat : ‖a - 1‖ ≤ t := by
    have h1 : ‖a - upsTilde C.hv 1‖ ≤ q := by
      have := hq.apply_le 1
      rw [norm_one, mul_one] at this
      simpa [LinearMap.sub_apply] using this
    have h2 : ‖upsTilde C.hv 1 - 1‖ ≤ C.δ / (1 - C.δ) := by
      have hlow := C.v_lower_one (upsTilde C.hv 1 - 1)
      rw [map_sub, v_upsTilde C.hv, tilde_one C.hA, norm_sub_rev (1 : H →L[ℂ] H)] at hlow
      rw [le_div_iff₀ hδ0]
      nlinarith [v_one C.hv]
    calc ‖a - 1‖ = ‖(a - upsTilde C.hv 1) + (upsTilde C.hv 1 - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖a - upsTilde C.hv 1‖ + ‖upsTilde C.hv 1 - 1‖ := norm_add_le _ _
      _ ≤ t := add_le_add h1 h2
  obtain ⟨c, hcsa, hcac, hc1⟩ := exists_normalizer hsa hat hsmall
  refine ⟨lrMul c c ∘ₗ upsPrime C π L, ⟨?_, ?_⟩, ?_⟩
  · change c * a * c = 1
    exact hcac
  · have := hcp.conj c
    rwa [hcsa.star_eq] at this
  · have ht0 : 0 ≤ t := by
      have : 0 ≤ C.δ / (1 - C.δ) := div_nonneg C.hδ hδ0.le
      linarith
    have hlr := lrMul_sub_id_cb c hc1 ht0
    have e : lrMul c c ∘ₗ upsPrime C π L - upsTilde C.hv
        = (lrMul c c - LinearMap.id) ∘ₗ upsPrime C π L + (upsPrime C π L - upsTilde C.hv) := by
      rw [LinearMap.sub_comp, LinearMap.id_comp]; abel
    rw [e]
    have := (hlr.comp (by positivity) (upsPrime_cb C π L hL hS)).add hq
    simpa using this

end Assemble

end Cert.KitaevChannels
