import LeanProof.Defs

/-!
# The inverse of a δ-isomorphism

Kitaev (arXiv:2405.02434, after Definition 2.2): "the inverse of a δ-isomorphism is a
(δ + O(δ²))-isomorphism". We prove it with the explicit constant `δ / (1 - δ)^3`.
-/

noncomputable section

namespace Kitaev

namespace DeltaIso

variable {δ ε ε' : ℝ} {A A' : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup A'] [NormedSpace ℂ A'] {S : EpsCStar ε A} {S' : EpsCStar ε' A'}

theorem norm_symm_le (v : DeltaIso δ S S') (hδ : δ < 1) (a : A') :
    ‖v.toEquiv.symm a‖ ≤ ‖a‖ / (1 - δ) := by
  have h := v.le_norm_map (v.toEquiv.symm a)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [le_div_iff₀ (by linarith)]
  linarith

private lemma aux₁ (hδ0 : 0 ≤ δ) (hδ : δ < 1) : δ / (1 - δ) ≤ δ / (1 - δ) ^ 3 := by
  have h1 : 0 < 1 - δ := by linarith
  apply div_le_div_of_nonneg_left hδ0 (by positivity)
  nlinarith [mul_pos h1 h1]

private lemma aux₂ (hδ0 : 0 ≤ δ) (hδ : δ < 1) : δ ≤ δ / (1 - δ) ^ 3 := by
  have h1 : 0 < 1 - δ := by linarith
  rw [le_div_iff₀ (by positivity)]
  have : (1 - δ) ^ 3 ≤ 1 := pow_le_one₀ h1.le (by linarith)
  nlinarith

/-- The inverse of a δ-isomorphism is a `δ / (1 - δ)^3`-isomorphism. -/
def symm (v : DeltaIso δ S S') (hδ0 : 0 ≤ δ) (hδ : δ < 1) :
    DeltaIso (δ / (1 - δ) ^ 3) S' S where
  toEquiv := v.toEquiv.symm
  map_star a := by
    apply v.toEquiv.injective
    rw [LinearEquiv.apply_symm_apply, v.map_star, LinearEquiv.apply_symm_apply]
  map_one_le := by
    have h1 : 0 < 1 - δ := by linarith
    have e : v.toEquiv.symm S'.one - S.one = v.toEquiv.symm (S'.one - v.toEquiv S.one) := by
      rw [map_sub, LinearEquiv.symm_apply_apply]
    rw [e]
    calc ‖v.toEquiv.symm (S'.one - v.toEquiv S.one)‖
        ≤ ‖S'.one - v.toEquiv S.one‖ / (1 - δ) := v.norm_symm_le hδ _
      _ ≤ δ / (1 - δ) := by
          rw [norm_sub_rev]
          exact div_le_div_of_nonneg_right v.map_one_le h1.le
      _ ≤ δ / (1 - δ) ^ 3 := aux₁ hδ0 hδ
  map_mul_le a b := by
    have h1 : 0 < 1 - δ := by linarith
    set x := v.toEquiv.symm a
    set y := v.toEquiv.symm b
    have ha : a = v.toEquiv x := by simp [x]
    have hb : b = v.toEquiv y := by simp [y]
    have e : v.toEquiv.symm (S'.mul a b) - S.mul x y
        = v.toEquiv.symm (S'.mul a b - v.toEquiv (S.mul x y)) := by
      rw [map_sub, LinearEquiv.symm_apply_apply]
    have hx : ‖x‖ ≤ ‖a‖ / (1 - δ) := v.norm_symm_le hδ a
    have hy : ‖y‖ ≤ ‖b‖ / (1 - δ) := v.norm_symm_le hδ b
    have hm : ‖S'.mul a b - v.toEquiv (S.mul x y)‖ ≤ δ * ‖x‖ * ‖y‖ := by
      rw [norm_sub_rev, ha, hb]
      simpa [x, y] using v.map_mul_le x y
    rw [e]
    calc ‖v.toEquiv.symm (S'.mul a b - v.toEquiv (S.mul x y))‖
        ≤ ‖S'.mul a b - v.toEquiv (S.mul x y)‖ / (1 - δ) := v.norm_symm_le hδ _
      _ ≤ δ * ‖x‖ * ‖y‖ / (1 - δ) := div_le_div_of_nonneg_right hm h1.le
      _ ≤ δ * (‖a‖ / (1 - δ)) * (‖b‖ / (1 - δ)) / (1 - δ) := by
          gcongr
      _ = δ / (1 - δ) ^ 3 * ‖a‖ * ‖b‖ := by
          field_simp
  le_norm_map a := by
    have h1 : 0 < 1 - δ := by linarith
    have hup := v.norm_map_le (v.toEquiv.symm a)
    rw [LinearEquiv.apply_symm_apply] at hup
    have h2 := aux₂ hδ0 hδ
    have hn : 0 ≤ ‖v.toEquiv.symm a‖ := norm_nonneg _
    have hna : 0 ≤ ‖a‖ := norm_nonneg _
    change (1 - δ / (1 - δ) ^ 3) * ‖a‖ ≤ ‖v.toEquiv.symm a‖
    have k1 : 0 ≤ (δ / (1 - δ) ^ 3 - δ) * ‖a‖ := mul_nonneg (sub_nonneg.2 h2) hna
    have k2 : (1 - δ) * ‖a‖ ≤ (1 - δ) * ((1 + δ) * ‖v.toEquiv.symm a‖) :=
      mul_le_mul_of_nonneg_left hup h1.le
    nlinarith [mul_nonneg (mul_nonneg hδ0 hδ0) hn]
  norm_map_le a := by
    have h1 : 0 < 1 - δ := by linarith
    change ‖v.toEquiv.symm a‖ ≤ (1 + δ / (1 - δ) ^ 3) * ‖a‖
    calc ‖v.toEquiv.symm a‖ ≤ ‖a‖ / (1 - δ) := v.norm_symm_le hδ a
      _ = (1 + δ / (1 - δ)) * ‖a‖ := by field_simp; ring
      _ ≤ (1 + δ / (1 - δ) ^ 3) * ‖a‖ :=
          mul_le_mul_of_nonneg_right (by linarith [aux₁ hδ0 hδ]) (norm_nonneg a)

end DeltaIso

end Kitaev
