import Certs.KitaevChannels.Delta

/-!
# The UCP map `Δ = c Δ'(·) c`, `c = Δ'(I)^{-1/2}`, and `‖Δ - Δ̃‖_cb = O(η)`
-/

open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {m : ℕ} {d : Fin m → ℕ}

theorem norm_one_le_one' {A : Type*} [CStarAlgebra A] : ‖(1 : A)‖ ≤ 1 :=
  norm_le_one_of_star_mul_self (by rw [star_one, one_mul])

theorem lrMul_sub_id {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (c : A) :
    lrMul c c - LinearMap.id = lrMul (c - 1) c + lrMul 1 (c - 1) := by
  ext x : 1
  simp only [LinearMap.sub_apply, LinearMap.add_apply, lrMul, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.id_apply]
  noncomm_ring

theorem lrMul_sub_id_cb {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (c : A)
    {t : ℝ} (hc : ‖c - 1‖ ≤ 2 * t) (ht : 0 ≤ t) :
    CBBound (lrMul c c - LinearMap.id) (2 * t * (2 + 2 * t)) := by
  rw [lrMul_sub_id]
  have h1 := (lrMul_cb (c - 1) c).add (lrMul_cb 1 (c - 1))
  refine h1.mono ?_
  have hc' : ‖c‖ ≤ 1 + 2 * t := by
    calc ‖c‖ = ‖(c - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖c - 1‖ + ‖(1 : A)‖ := norm_add_le _ _
      _ ≤ 2 * t + 1 := add_le_add hc norm_one_le_one'
      _ = 1 + 2 * t := by ring
  have h1n := norm_one_le_one' (A := A)
  have hcn := norm_nonneg (c - 1)
  have hcn' := norm_nonneg c
  have e1 : ‖c - 1‖ * ‖c‖ ≤ 2 * t * (1 + 2 * t) := mul_le_mul hc hc' hcn' (by positivity)
  have e2 : ‖(1 : A)‖ * ‖c - 1‖ ≤ 1 * (2 * t) := mul_le_mul h1n hc hcn (by norm_num)
  nlinarith

section Build

variable [Nontrivial H] (hF : CPMapFacts) {Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)} {η δ : ℝ}
  {v : BlockAlg d →ₗ[ℂ] (H →L[ℂ] H)}
  (hv : IsExtDeltaIsoOnto δ (LinearMap.range (tildePhi Φ).toLinearMap) (choiEffros Φ) v)
  (D : (j : Fin m) → Design (d j))
include hF hv D

/-- **The UCP map `Δ`** with `‖Δ - Δ̃‖_cb ≤ 2t(2+2t)(1+δ+K) + K`, where `K = 12η(1+δ)² + δ` and
`t = K + δ ≤ 1/2`. -/
theorem exists_Delta (hΦ : IsUCP Φ.toLinearMap) (hcb : CBBound (Φ * Φ - Φ).toLinearMap η)
    (hη : 0 ≤ η) (hη8 : η ≤ 1 / 8) (hδ : 0 ≤ δ)
    (hsmall : 12 * η * (1 + δ) ^ 2 + δ + δ ≤ 1 / 2) :
    ∃ Δ : BlockAlg d →ₗ[ℂ] (H →L[ℂ] H), IsUCP Δ ∧
      CBBound (Δ - v) (2 * (12 * η * (1 + δ) ^ 2 + δ + δ) * (2 + 2 * (12 * η * (1 + δ) ^ 2 + δ + δ))
        * (1 + δ + (12 * η * (1 + δ) ^ 2 + δ)) + (12 * η * (1 + δ) ^ 2 + δ)) := by
  set K := 12 * η * (1 + δ) ^ 2 + δ with hK
  set t := K + δ with ht
  have hK0 : 0 ≤ K := by positivity
  have hDP := DeltaP_sub_cb hF hv D hΦ hcb hη hη8 hδ
  rw [← hK] at hDP
  have hcp : IsCP (DeltaP Φ v D) := DeltaP_cp hΦ.2 (v_star hv) D
  set a := DeltaP Φ v D 1 with ha
  have hsa : IsSelfAdjoint a := by
    have := star_of_cp hF hcp 1
    rw [star_one] at this
    exact this.symm
  have hat : ‖a - 1‖ ≤ t := by
    have h1 : ‖a - v 1‖ ≤ K * ‖(1 : BlockAlg d)‖ := by
      have := hDP.apply_le 1
      simpa [LinearMap.sub_apply] using this
    have h2 : ‖v 1 - 1‖ ≤ δ := v_one hv
    have h3 : K * ‖(1 : BlockAlg d)‖ ≤ K := by
      have := norm_one_le_one' (A := BlockAlg d)
      nlinarith
    calc ‖a - 1‖ = ‖(a - v 1) + (v 1 - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖a - v 1‖ + ‖v 1 - 1‖ := norm_add_le _ _
      _ ≤ K + δ := by linarith
  obtain ⟨c, hcsa, hcac, hc1⟩ := exists_normalizer hsa hat hsmall
  refine ⟨lrMul c c ∘ₗ DeltaP Φ v D, ⟨?_, ?_⟩, ?_⟩
  · change c * a * c = 1
    exact hcac
  · have := hcp.conj c
    rwa [hcsa.star_eq] at this
  · have ht0 : 0 ≤ t := by positivity
    have hlr := lrMul_sub_id_cb c hc1 ht0
    have hDPcb : CBBound (DeltaP Φ v D) (1 + δ + K) := by
      have := (v_cb hv).add hDP
      simpa using this
    have e : lrMul c c ∘ₗ DeltaP Φ v D - v =
        (lrMul c c - LinearMap.id) ∘ₗ DeltaP Φ v D + (DeltaP Φ v D - v) := by
      rw [LinearMap.sub_comp, LinearMap.id_comp]; abel
    rw [e]
    exact (hlr.comp (by positivity) hDPcb).add hDP

end Build

end Cert.KitaevChannels
