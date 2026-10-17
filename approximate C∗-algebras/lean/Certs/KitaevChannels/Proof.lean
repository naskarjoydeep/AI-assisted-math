import Certs.KitaevChannels.Final
import Certs.KitaevChannels.Arith

/-!
# Proof of Theorem A (Kitaev's Theorem 12.3 on a Hilbert space of any dimension)

Informal proof (note `infinite_dim.tex`, Theorem A; Kitaev §12.2), with Stinespring dilations in
place of Kitaev's two Choi representations:

* T1. Theorem 12.1 makes `Im Φ̃` an extended `(c₁η)`-C* algebra; Theorem 10.5 (it is
  finite-dimensional) gives `v : ⊕ⱼ M_{dⱼ} → Im Φ̃`, a `δ`-isomorphism, `δ = C₃c₁η`.
* T2. `Δ' = ∑ₛ pₛ Φ(v(· uₛ†) v(uₛ))` over a signed product design (Kitaev's unsigned product is
  not a diagonal for ≥ 2 blocks), normalized by `Δ'(1)^{-1/2}`: UCP with `‖Δ - v‖_cb ≤ e`.
* T3. (12.34)–(12.36) at every matrix level, (12.36) from Kitaev's (12.6).
* T4. Stinespring `Δ = W†ρ(·)W`; Lemma 12.4 for `R = ∑ pₜ ρ(Uₜ†)WW†ρ(Uₜ)`; an approximate
  maximizer `ζ` (the norm of `R` need not be attained); `L = ∑ pₛ π(Δ(Uₛ†)) V W† ρ(Uₛ) J`.
* T5. `Υ' ≈ Υ'Φ ≈ Υ'Φ̃ = Υ'vΥ̃ ≈ Υ'ΔΥ̃ ≈ Υ̃`; `Υ = Υ'(1)^{-1/2} Υ'(·) Υ'(1)^{-1/2}`.
* T6. For `η = 0` the slack `τ > 0` of the maximizer would spoil the exact bound; there `v` is a
  unital complete isometry and `Υ̃` itself is UCP.
* T7. `ΔΥ - Φ = (Δ - v)Υ + v(Υ - Υ̃) + (Φ̃ - Φ)`, `Υ(ΔXΔY) ≈ Υ̃(ΔXΔY) = v⁻¹Φ̃(ΔXΔY) ≈ XY`;
  explicit constants `η₀ = min(η₁, η₂, ε₃/(c₁+1), 1/(2·10⁵ Λ))`, `C = 10⁶ Λ`,
  `Λ = C₃c₁ + c₂ + 1`.
-/

open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace Cert.KitaevChannels

theorem IsExtDeltaIsoOnto.mono {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {m : ℕ} {d : Fin m → ℕ} {δ δ' : ℝ} {A : Submodule ℂ (H →L[ℂ] H)}
    {mul : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {v : BlockAlg d →ₗ[ℂ] (H →L[ℂ] H)}
    (h : IsExtDeltaIsoOnto δ A mul v) (hδ : δ ≤ δ') : IsExtDeltaIsoOnto δ' A mul v := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.trans hδ, fun n X Y => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2.2.2.2 n X Y
  have hX := norm_nonneg X
  have hY := norm_nonneg Y
  refine ⟨h1.trans ?_, le_trans ?_ h2, h3.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδ hX) hY
  · exact mul_le_mul_of_nonneg_right (by linarith) hX
  · exact mul_le_mul_of_nonneg_right (by linarith) hX

set_option maxHeartbeats 2000000 in
theorem main : Claim := by
  intro hF hS hD c₁ η₁ c₂ η₂ C₃ ε₃ hc₁ hη₁ hc₂ hη₂ hC₃ hε₃ K121 K126 K105
  set Λ : ℝ := C₃ * c₁ + c₂ + 1 with hΛdef
  have hC₃c₁ := mul_nonneg hC₃ hc₁
  have hΛ1 : 1 ≤ Λ := by linarith
  have hΛ0 : 0 < Λ := by linarith
  refine ⟨min (min η₁ η₂) (min (ε₃ / (c₁ + 1)) (1 / (200000 * Λ))), 1000000 * Λ, ?_, ?_⟩
  · exact lt_min (lt_min hη₁ hη₂) (lt_min (div_pos hε₃ (by linarith)) (by positivity))
  intro H _ _ _ _ Φ η hΦ hcb hη hηlt hfin
  have hlt1 : η < η₁ := lt_of_lt_of_le hηlt ((min_le_left _ _).trans (min_le_left _ _))
  have hlt2 : η < η₂ := lt_of_lt_of_le hηlt ((min_le_left _ _).trans (min_le_right _ _))
  have hlt3 : η < ε₃ / (c₁ + 1) :=
    lt_of_lt_of_le hηlt ((min_le_right _ _).trans (min_le_left _ _))
  have hlt4 : η < 1 / (200000 * Λ) :=
    lt_of_lt_of_le hηlt ((min_le_right _ _).trans (min_le_right _ _))
  set x := Λ * η with hxdef
  have hx : x ≤ 1 / 200000 := by
    rw [lt_div_iff₀ (by positivity)] at hlt4
    rw [hxdef]; nlinarith
  have hηx : η ≤ x := by rw [hxdef]; nlinarith
  have hc₂x : c₂ * η ≤ x := by rw [hxdef, hΛdef]; nlinarith [mul_nonneg hC₃c₁ hη]
  have hc₁η : c₁ * η < ε₃ := by
    rw [lt_div_iff₀ (by linarith)] at hlt3; nlinarith
  have hη8 : η ≤ 1 / 8 := by linarith
  -- T1: Theorems 12.1 and 10.5
  have hA := K121 H Φ η hΦ hcb hη hlt1
  haveI := hfin
  obtain ⟨m, d, v, hv⟩ := K105 H (LinearMap.range (tildePhi Φ).toLinearMap) (choiEffros Φ)
    (c₁ * η) (mul_nonneg hc₁ hη) hc₁η hA
  set δ := C₃ * (c₁ * η) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hδx : δ ≤ x := by
    rw [hδdef, hxdef, hΛdef]; nlinarith [mul_nonneg hc₂ hη]
  obtain ⟨hsmall, heb⟩ := arith_delta hη hηx hδ0 hδx hx
  -- T2: the UCP map `Δ`
  obtain ⟨Δ, hΔ, hΔv⟩ := exists_Delta hF hv (fun j => Design.ofHyp hD (d j)) hΦ hcb hη hη8 hδ0
    hsmall
  set e := 2 * (12 * η * (1 + δ) ^ 2 + δ + δ) * (2 + 2 * (12 * η * (1 + δ) ^ 2 + δ + δ))
    * (1 + δ + (12 * η * (1 + δ) ^ 2 + δ)) + (12 * η * (1 + δ) ^ 2 + δ) with hedef
  have he0 : 0 ≤ e := by positivity
  let ctx : Ctx H := Ctx.mk Φ η δ e (c₁ * η) m d v Δ hF hA hv hΦ hcb hη hη8 hδ0 hΔ hΔv he0
  have hδ1 : ctx.δ < 1 := by show δ < 1; linarith
  -- T7 constants
  obtain ⟨hκ0, ht', hQ0', hQb', hfin2⟩ := arith_main (x := x) (η := ctx.η) (δ := ctx.δ)
    (e := ctx.e) (c₂ := c₂) (e34 := ctx.e34) (e35 := ctx.e35) (e36 := ctx.e36 c₂)
    (κ := 4 * (ctx.e34 + ctx.e36 c₂) + 2 * (ctx.δ + ctx.e + ctx.e35 + ctx.η))
    (u := (1 + 12 * ctx.η) / (1 - ctx.δ))
    (q := ctx.η + 12 * ctx.η + ctx.e * ((1 + 12 * ctx.η) / (1 - ctx.δ))
      + (4 * (ctx.e34 + ctx.e36 c₂) + 2 * (ctx.δ + ctx.e + ctx.e35 + ctx.η))
        * ((1 + 12 * ctx.η) / (1 - ctx.δ)))
    hη hηx hδ0 hδx hc₂ hc₂x he0 heb hx rfl rfl rfl rfl rfl rfl rfl rfl
  -- T4: Stinespring dilations of `Δ` and `Φ`
  obtain ⟨K, _, _, _, ρ, W, hW⟩ := (hS (BlockAlg d) H Δ).1 hΔ.2
  obtain ⟨K', _, _, _, π, V, hV⟩ := (hS (H →L[ℂ] H) H Φ.toLinearMap).1 hΦ.2
  have hK2 := K126 H Φ η hΦ hcb hη hlt2
  -- T4–T6: the UCP map `Υ`
  obtain ⟨Υ, hΥ, Q, hQ, hQ0, hQb⟩ : ∃ Υ : (H →L[ℂ] H) →ₗ[ℂ] BlockAlg d, IsUCP Υ ∧
      ∃ Q : ℝ, CBBound (Υ - upsTilde ctx.hv) Q ∧ 0 ≤ Q ∧ Q ≤ 264000 * x := by
    rcases hη.eq_or_lt with h0 | hpos
    · have hδz : ctx.δ = 0 := by show δ = 0; rw [hδdef, ← h0]; ring
      refine ⟨upsTilde ctx.hv, ctx.upsTilde_ucp_exact hδz h0.symm, 0, ?_, le_rfl,
        by rw [hxdef, ← h0, mul_zero, mul_zero]⟩
      rw [sub_self]; exact CBBound.zero
    · have hb := fun j => block_bound ctx ρ W π V hS hW hV hc₂ hK2 j (Design.ofHyp hD (d j)) hpos
      choose L hL hLb using hb
      have hq := upsPrime_close ctx π L hL hS hδ1 hκ0 hLb
      obtain ⟨Υ, hΥ, hΥq⟩ := exists_Ups ctx π L hL hS hδ1 hq ht'
      exact ⟨Υ, hΥ, _, hΥq, hQ0', hQb'⟩
  -- T7: the conclusions
  obtain ⟨hf1, hf2⟩ := ctx.final_bounds Υ hΥ hQ hQ0 hδ1
  have hxη : 1000000 * Λ * η = 1000000 * x := by rw [hxdef]; ring
  refine ⟨m, d, v, Δ, Υ, hv.mono ?_, hΔ, hΥ, hf1.mono ?_, fun n X Y => (hf2 n X Y).trans ?_⟩
  · rw [hxη]; linarith
  · rw [hxη]
    have h1 : (1 + ctx.δ) * Q ≤ 2 * Q := by
      have : ctx.δ ≤ 1 := hδ1.le
      nlinarith
    have h2 : ctx.e ≤ 200 * x := heb
    have h3 : 12 * ctx.η ≤ 12 * x := by show 12 * η ≤ 12 * x; linarith
    linarith
  · rw [hxη]
    have hXY := mul_nonneg (norm_nonneg X) (norm_nonneg Y)
    have hc : Q + (12 * ctx.η + ctx.e35 + ctx.e) / (1 - ctx.δ) ≤ 1000000 * x := by linarith
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hc hXY

end Cert.KitaevChannels
