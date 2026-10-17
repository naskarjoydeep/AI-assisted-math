import Certs.KitaevChannels.Stine

/-!
# Kitaev's Lemma 12.4, any dimension: `‖R‖ ≥ 1 - O(η)`, and an approximate maximizer `ζ`

Kitaev picks `ξⱼ ∈ Eⱼ` with `‖Cⱼ ξⱼ‖ ≈ 1`; when `dim Eⱼ = ∞` the norm need not be attained, so we
pick `ζ` in the range of `ρ(E₀₀)` with `‖R ζ‖ ≥ ‖R‖ - τ`.
-/

open scoped ComplexOrder InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

namespace Ctx

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
  (C : Ctx H)

/-- `(12.35)` at level one. -/
theorem mul35_one (x y : BlockAlg C.d) :
    ‖C.Φ (C.Δ x * C.Δ y) - C.Δ (x * y)‖ ≤ C.e35 * ‖x‖ * ‖y‖ := by
  have h := C.mul35 (diagM 1 x) (diagM 1 y)
  rw [amp_diagM, amp_diagM, diagM_mul, amp_diagM, diagM_mul, amp_diagM,
    show diagM 1 (C.Φ.toLinearMap (C.Δ x * C.Δ y)) - diagM 1 (C.Δ (x * y))
      = diagM 1 (C.Φ (C.Δ x * C.Δ y) - C.Δ (x * y)) from
      (map_sub (diagHom (M₂ := H →L[ℂ] H) 1) _ _).symm,
    norm_diagM_one, norm_diagM_one, norm_diagM_one] at h
  exact h

/-- Level-one lower bound for `v`. -/
theorem v_lower_one (x : BlockAlg C.d) : (1 - C.δ) * ‖x‖ ≤ ‖C.v x‖ := by
  have h := v_lower C.hv (diagM 1 x)
  rwa [amp_diagM, norm_diagM_one, norm_diagM_one] at h

end Ctx

theorem sum_E_diag {d : ℕ} : ∑ a : Fin d, E a a = 1 := by
  refine CStarMatrix.ext fun i k => ?_
  rw [cm_sum_apply, CStarMatrix.one_apply]
  change ∑ a, (Matrix.single a a (1 : ℂ)) i k = _
  simp only [Matrix.single_apply]
  by_cases h : i = k
  · subst h; simp
  · simp [h]

section Stinespring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
  (C : Ctx H)
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (ρ : BlockAlg C.d →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K)
  (hW : ∀ x, C.Δ x = ContinuousLinearMap.adjoint W ∘L ρ x ∘L W)
include hW

theorem W_norm_le : ‖W‖ ≤ 1 := by
  have h1 : ContinuousLinearMap.adjoint W ∘L W = 1 := by
    have := hW 1
    rw [C.hΔ.1, map_one, show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl,
      ContinuousLinearMap.id_comp] at this
    exact this.symm
  have h2 := ContinuousLinearMap.norm_adjoint_comp_self W
  rw [h1] at h2
  have h3 : ‖(1 : H →L[ℂ] H)‖ = 1 := norm_one
  nlinarith [norm_nonneg W]

theorem Wadj_norm_le : ‖ContinuousLinearMap.adjoint W‖ ≤ 1 := by
  rw [LinearIsometryEquiv.norm_map]; exact W_norm_le C ρ W hW

variable (j : Fin C.m) (Dj : Design (C.d j))

/-- `W† R W = ∑ₜ pₜ Δ(ιⱼ U_t†) Δ(ιⱼ U_t)`. -/
theorem W_R_W : ContinuousLinearMap.adjoint W ∘L Rop ρ W j Dj ∘L W =
    ∑ t, (Dj.p t : ℂ) • (C.Δ (ιb j (star (Dj.U t))) * C.Δ (ιb j (Dj.U t))) := by
  unfold Rop
  rw [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hW, hW, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rfl

/-- **Lemma 12.4 (lower bound)**: `‖R‖ ≥ 1 - δ - e - e35` when the block is nonzero. -/
theorem Rop_norm_ge (hdj : 0 < C.d j) : 1 - C.δ - C.e - C.e35 ≤ ‖Rop ρ W j Dj‖ := by
  have : Nonempty (Fin (C.d j)) := ⟨⟨0, hdj⟩⟩
  have hU : ∀ t, ‖Dj.U t‖ ≤ 1 := fun t => norm_le_one_of_star_mul_self (Dj.unit t).1
  have hUs : ∀ t, ‖star (Dj.U t)‖ ≤ 1 := fun t =>
    norm_le_one_of_star_mul_self (by rw [star_star]; exact (Dj.unit t).2)
  -- `Φ(W† R W) ≈ Δ(ιⱼ 1)`
  have hsum1 : C.Δ (ιb j 1) = ∑ t, (Dj.p t : ℂ) • C.Δ (ιb j (star (Dj.U t)) * ιb j (Dj.U t)) := by
    simp only [← ιb_mul, (Dj.unit _).1]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, Dj.p_sum, Complex.ofReal_one, one_smul]
  have hclose : ‖C.Φ (ContinuousLinearMap.adjoint W ∘L Rop ρ W j Dj ∘L W) - C.Δ (ιb j 1)‖
      ≤ C.e35 := by
    rw [W_R_W C ρ W hW j Dj, hsum1, map_sum, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ t, ‖C.Φ ((Dj.p t : ℂ) • (C.Δ (ιb j (star (Dj.U t))) * C.Δ (ιb j (Dj.U t))))
        - (Dj.p t : ℂ) • C.Δ (ιb j (star (Dj.U t)) * ιb j (Dj.U t))‖ ≤ Dj.p t * C.e35 := fun t => by
      rw [map_smul, ← smul_sub, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Dj.p_nonneg t)]
      refine mul_le_mul_of_nonneg_left ?_ (Dj.p_nonneg t)
      refine (C.mul35_one _ _).trans ?_
      rw [norm_ιb, norm_ιb]
      have := C.e35_nonneg
      have h1 := hUs t
      have h2 := hU t
      have h3 := norm_nonneg (star (Dj.U t))
      have h4 := norm_nonneg (Dj.U t)
      nlinarith [mul_le_mul h1 h2 h4 zero_le_one]
    refine (Finset.sum_le_sum fun t _ => hterm t).trans ?_
    rw [← Finset.sum_mul, Dj.p_sum, one_mul]
  -- `‖Δ(ιⱼ 1)‖ ≥ 1 - δ - e`
  have hΔ1 : 1 - C.δ - C.e ≤ ‖C.Δ (ιb j 1)‖ := by
    have hn : ‖ιb (d := C.d) j (1 : Mat (C.d j) ℂ)‖ = 1 := by rw [norm_ιb, norm_one]
    have hlow := C.v_lower_one (ιb j 1)
    have hdiff : ‖C.Δ (ιb j 1) - C.v (ιb j 1)‖ ≤ C.e * ‖ιb (d := C.d) j (1 : Mat (C.d j) ℂ)‖ := by
      have := C.hΔv.apply_le (ιb j 1)
      simpa [LinearMap.sub_apply] using this
    rw [hn] at hlow hdiff
    have := norm_sub_norm_le (C.v (ιb j 1)) (C.Δ (ιb j 1))
    rw [norm_sub_rev] at hdiff
    linarith
  -- `‖Φ(W† R W)‖ ≤ ‖R‖`
  have hΦle : ‖C.Φ (ContinuousLinearMap.adjoint W ∘L Rop ρ W j Dj ∘L W)‖ ≤ ‖Rop ρ W j Dj‖ := by
    have h1 := C.phi_cb.apply_le (ContinuousLinearMap.adjoint W ∘L Rop ρ W j Dj ∘L W)
    rw [one_mul] at h1
    refine h1.trans ?_
    calc ‖ContinuousLinearMap.adjoint W ∘L Rop ρ W j Dj ∘L W‖
        ≤ ‖ContinuousLinearMap.adjoint W‖ * ‖Rop ρ W j Dj ∘L W‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (‖Rop ρ W j Dj‖ * 1) := by
          refine mul_le_mul (Wadj_norm_le C ρ W hW) ?_ (norm_nonneg _) zero_le_one
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (W_norm_le C ρ W hW) (norm_nonneg _))
      _ = ‖Rop ρ W j Dj‖ := by ring
  have := norm_sub_norm_le (C.Δ (ιb j 1)) (C.Φ (ContinuousLinearMap.adjoint W ∘L Rop ρ W j Dj ∘L W))
  rw [norm_sub_rev] at this
  linarith

end Stinespring

section MatUnitsK

variable {m : ℕ} {d : Fin m → ℕ}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (ρ : BlockAlg d →⋆ₐ[ℂ] (K →L[ℂ] K)) (j : Fin m)

/-- Matrix units of block `j` in the Stinespring space. -/
abbrev Pu (a b : Fin (d j)) : K →L[ℂ] K := ρ (ιb j (E a b))

theorem Pu_mul (a b c e : Fin (d j)) :
    Pu ρ j a b * Pu ρ j c e = if b = c then Pu ρ j a e else 0 := by
  rw [Pu, Pu, ← map_mul, ← ιb_mul, E_mul_E]
  split_ifs
  · rfl
  · rw [map_zero, map_zero]

theorem Pu_adj (a b : Fin (d j)) : ContinuousLinearMap.adjoint (Pu ρ j a b) = Pu ρ j b a := by
  rw [← ContinuousLinearMap.star_eq_adjoint, Pu, ← map_star, ← ιb_star, star_E]

theorem Pu_sum : ∑ a, Pu ρ j a a = ρ (ιb j 1) := by
  rw [← sum_E_diag, map_sum, map_sum]

end MatUnitsK

end Cert.KitaevChannels
