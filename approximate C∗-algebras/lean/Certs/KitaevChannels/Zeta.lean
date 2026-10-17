import Certs.KitaevChannels.Lemma124

/-!
# The approximate maximizer `ζ` and Kitaev's `1 ⊗ ξ` without tensor factors

Kitaev writes `R_j = 1 ⊗ C_j` and picks a unit `ξ_j` with `‖C_j ξ_j‖ ≈ 1`. Here `R` is any operator
commuting with the matrix units `P_ab = ρ(ιⱼ E_ab)` and supported on `ρ(ιⱼ 1)`. We show
`‖R‖ ≤ ‖R P_oo‖`, pick `ζ = P_oo κ` with `‖R ζ‖ ≥ ‖R‖ - τ` (the norm need not be attained in
infinite dimensions), and replace `U ⊗ ξ` by `ρ(ιⱼ U) J` with `J e_b = P_bo ζ`.
-/

open scoped ComplexOrder InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

theorem norm_E_le {d : ℕ} (a b : Fin d) : ‖E a b‖ ≤ 1 := by
  have hP : ‖E b b‖ ≤ 1 := by
    have h := CStarRing.norm_star_mul_self (x := E b b)
    rw [star_E, E_mul_E, if_pos rfl] at h
    nlinarith [norm_nonneg (E b b)]
  have h := CStarRing.norm_star_mul_self (x := E a b)
  rw [star_E, E_mul_E, if_pos rfl] at h
  nlinarith [norm_nonneg (E a b)]

section Zeta

variable {m : ℕ} {d : Fin m → ℕ}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (ρ : BlockAlg d →⋆ₐ[ℂ] (K →L[ℂ] K)) (j : Fin m)

theorem norm_rho_le (x : BlockAlg d) : ‖ρ x‖ ≤ ‖x‖ := NonUnitalStarAlgHom.norm_apply_le ρ x

theorem rho_adj (x : BlockAlg d) : ContinuousLinearMap.adjoint (ρ x) = ρ (star x) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, map_star]

theorem norm_Pu_le (a b : Fin (d j)) : ‖Pu ρ j a b‖ ≤ 1 :=
  (norm_rho_le ρ _).trans (by rw [norm_ιb]; exact norm_E_le a b)

theorem norm_rho_one_le : ‖ρ (ιb j 1)‖ ≤ 1 :=
  (norm_rho_le ρ _).trans (by rw [norm_ιb]; exact norm_one_le_one')

/-- Pythagoras across the rows of block `j`: `‖ρ(ιⱼ1) y‖² = ∑ₐ ‖P_oa y‖²`. -/
theorem pyth (o : Fin (d j)) (y : K) : ‖ρ (ιb j 1) y‖ ^ 2 = ∑ a, ‖Pu ρ j o a y‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ),
    ← ContinuousLinearMap.adjoint_inner_right (ρ (ιb j 1)) y (ρ (ιb j 1) y), rho_adj,
    ← ιb_star, star_one, ← mul_apply_eq_comp, ← map_mul, ← ιb_mul, one_mul,
    ← Pu_sum, ContinuousLinearMap.sum_apply, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show Pu ρ j a a = Pu ρ j a o * Pu ρ j o a by rw [Pu_mul, if_pos rfl],
    mul_apply_eq_comp, ← Pu_adj ρ j o a, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq]

/-- `‖T‖ ≤ ‖T P_oo‖` for `T` commuting with the matrix units of block `j` and supported there. -/
theorem norm_le_norm_comp_P (o : Fin (d j)) (T : K →L[ℂ] K)
    (hc : ∀ a b, T * Pu ρ j a b = Pu ρ j a b * T) (hs : ρ (ιb j 1) * T = T) :
    ‖T‖ ≤ ‖T * Pu ρ j o o‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun κ => ?_
  set N := ‖T * Pu ρ j o o‖
  have hN : 0 ≤ N := norm_nonneg _
  have h1 : ‖T κ‖ ^ 2 = ∑ a, ‖(T * Pu ρ j o o) (Pu ρ j o a κ)‖ ^ 2 := by
    have := pyth ρ j o (T κ)
    rw [← mul_apply_eq_comp, hs] at this
    rw [this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← mul_apply_eq_comp, ← hc, ← mul_apply_eq_comp, mul_assoc, Pu_mul,
      if_pos rfl]
  have h2 : ∑ a, ‖(T * Pu ρ j o o) (Pu ρ j o a κ)‖ ^ 2 ≤ ∑ a, N ^ 2 * ‖Pu ρ j o a κ‖ ^ 2 := by
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
  have h3 : ∑ a, ‖Pu ρ j o a κ‖ ^ 2 ≤ ‖κ‖ ^ 2 := by
    rw [← pyth ρ j o κ]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    calc ‖ρ (ιb j 1) κ‖ ≤ ‖ρ (ιb j 1)‖ * ‖κ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖κ‖ := mul_le_mul_of_nonneg_right (norm_rho_one_le ρ j) (norm_nonneg _)
      _ = ‖κ‖ := one_mul _
  rw [← Finset.mul_sum] at h2
  have h4 : ‖T κ‖ ^ 2 ≤ (N * ‖κ‖) ^ 2 := by
    rw [mul_pow]
    calc ‖T κ‖ ^ 2 ≤ N ^ 2 * ∑ a, ‖Pu ρ j o a κ‖ ^ 2 := h1 ▸ h2
      _ ≤ N ^ 2 * ‖κ‖ ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4

/-- **The approximate maximizer**: `ζ ∈ Im P_oo`, `‖ζ‖ ≤ 1`, `‖T ζ‖ ≥ ‖T‖ - τ`. -/
theorem exists_zeta (o : Fin (d j)) (T : K →L[ℂ] K)
    (hc : ∀ a b, T * Pu ρ j a b = Pu ρ j a b * T) (hs : ρ (ιb j 1) * T = T) {τ : ℝ} (hτ : 0 < τ) :
    ∃ ζ : K, Pu ρ j o o ζ = ζ ∧ ‖ζ‖ ≤ 1 ∧ ‖T‖ - τ ≤ ‖T ζ‖ := by
  have hle := norm_le_norm_comp_P ρ j o T hc hs
  obtain ⟨κ, hκ, hlt⟩ := (T * Pu ρ j o o).exists_lt_apply_of_lt_opNorm
    (show ‖T‖ - τ < ‖T * Pu ρ j o o‖ by linarith)
  refine ⟨Pu ρ j o o κ, ?_, ?_, ?_⟩
  · rw [← mul_apply_eq_comp, Pu_mul, if_pos rfl]
  · calc ‖Pu ρ j o o κ‖ ≤ ‖Pu ρ j o o‖ * ‖κ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_Pu_le ρ j o o) hκ.le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [mul_apply_eq_comp] at hlt
    exact hlt.le

end Zeta

section Jop

variable {m : ℕ} {d : Fin m → ℕ}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (ρ : BlockAlg d →⋆ₐ[ℂ] (K →L[ℂ] K)) (j : Fin m) (o : Fin (d j)) (ζ : K)

/-- `J : ℂ^{dⱼ} → K`, `J e_b = P_bo ζ` (Kitaev's `1 ⊗ ξ`). -/
def Jop : EuclideanSpace ℂ (Fin (d j)) →L[ℂ] K :=
  ∑ b, (EuclideanSpace.proj b : EuclideanSpace ℂ (Fin (d j)) →L[ℂ] ℂ).smulRight (Pu ρ j b o ζ)

theorem Jop_apply (x : EuclideanSpace ℂ (Fin (d j))) :
    Jop ρ j o ζ x = ∑ b, x b • Pu ρ j b o ζ := by
  simp [Jop, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

theorem Pu_sandwich (Q : K →L[ℂ] K) (hQ : ∀ a b, Q * Pu ρ j a b = Pu ρ j a b * Q)
    (Y : Mat (d j) ℂ) (a b : Fin (d j)) :
    Pu ρ j o a * ρ (ιb j Y) * Q * Pu ρ j b o = Y a b • (Pu ρ j o o * Q) := by
  rw [mul_assoc (Pu ρ j o a * ρ (ιb j Y)) Q (Pu ρ j b o), hQ, ← mul_assoc, Pu, Pu,
    ← map_mul, ← map_mul, ← ιb_mul, ← ιb_mul, E_Y_E, map_smul, map_smul, smul_mul_assoc]

/-- `J† ρ(ιⱼY) Q J = ⟨ζ, Qζ⟩ · Y` for `Q` commuting with the matrix units. -/
theorem J_sandwich (hζ : Pu ρ j o o ζ = ζ) (Q : K →L[ℂ] K)
    (hQ : ∀ a b, Q * Pu ρ j a b = Pu ρ j a b * Q) (Y : Mat (d j) ℂ) :
    ContinuousLinearMap.adjoint (Jop ρ j o ζ) ∘L (ρ (ιb j Y) * Q) ∘L Jop ρ j o ζ
      = ⟪ζ, Q ζ⟫_ℂ • matCLM (d j) Y := by
  refine ContinuousLinearMap.ext fun x => ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply, Jop_apply, Jop_apply, ContinuousLinearMap.smul_apply,
    inner_smul_right, sum_inner]
  have hent : ∀ a b, ⟪Pu ρ j a o ζ, (ρ (ιb j Y) * Q) (Pu ρ j b o ζ)⟫_ℂ = Y a b * ⟪ζ, Q ζ⟫_ℂ :=
    fun a b => by
      rw [← Pu_adj ρ j o a, ContinuousLinearMap.adjoint_inner_left, ← mul_apply_eq_comp,
        ← mul_apply_eq_comp, ← mul_assoc, Pu_sandwich ρ j o Q hQ Y a b,
        ContinuousLinearMap.smul_apply, inner_smul_right, mul_apply_eq_comp,
        ← ContinuousLinearMap.adjoint_inner_left, Pu_adj, hζ]
  simp only [map_sum, map_smul, inner_sum, inner_smul_left, inner_smul_right, hent]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [matCLM, StarAlgEquiv.trans_apply, Matrix.ofLp_toEuclideanCLM, dotProduct,
    Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change x b * ((starRingEnd ℂ) (y a) * (Y a b * ⟪ζ, Q ζ⟫_ℂ))
    = ⟪ζ, Q ζ⟫_ℂ * (Y a b * x b * (starRingEnd ℂ) (y a))
  ring

theorem rho_one_comp_J : ρ (ιb j 1) ∘L Jop ρ j o ζ = Jop ρ j o ζ := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.comp_apply, Jop_apply, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, ← mul_apply_eq_comp, ← map_mul, ← ιb_mul, one_mul]

theorem J_adj_J (hζ : Pu ρ j o o ζ = ζ) :
    ContinuousLinearMap.adjoint (Jop ρ j o ζ) ∘L Jop ρ j o ζ = ⟪ζ, ζ⟫_ℂ • 1 := by
  have h := J_sandwich ρ j o ζ hζ 1 (fun a b => by rw [one_mul, mul_one]) 1
  rw [mul_one, rho_one_comp_J, map_one, show (1 : K →L[ℂ] K) ζ = ζ from rfl] at h
  exact h

theorem norm_J_le (hζ : Pu ρ j o o ζ = ζ) (hζn : ‖ζ‖ ≤ 1) : ‖Jop ρ j o ζ‖ ≤ 1 := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self (Jop ρ j o ζ)
  rw [J_adj_J ρ j o ζ hζ] at h
  have h1 : ‖⟪ζ, ζ⟫_ℂ • (1 : EuclideanSpace ℂ (Fin (d j)) →L[ℂ] EuclideanSpace ℂ (Fin (d j)))‖
      ≤ 1 := by
    refine (norm_smul_le ⟪ζ, ζ⟫_ℂ
      (1 : EuclideanSpace ℂ (Fin (d j)) →L[ℂ] EuclideanSpace ℂ (Fin (d j)))).trans ?_
    have := norm_inner_le_norm (𝕜 := ℂ) ζ ζ
    have h1 : ‖(1 : EuclideanSpace ℂ (Fin (d j)) →L[ℂ] EuclideanSpace ℂ (Fin (d j)))‖ ≤ 1 :=
      norm_one_le_one'
    have := norm_nonneg ζ
    have := norm_nonneg ⟪ζ, ζ⟫_ℂ
    nlinarith
  have := norm_nonneg (Jop ρ j o ζ)
  nlinarith

/-- `J† T ρ(y) T J = ‖Tζ‖² · y_j` for self-adjoint `T` commuting with `ρ(ιⱼ M_{dⱼ})`, supported in
block `j`. -/
theorem T_sandwich (hζ : Pu ρ j o o ζ = ζ) (T : K →L[ℂ] K)
    (hcY : ∀ Y, T * ρ (ιb j Y) = ρ (ιb j Y) * T) (hsa : IsSelfAdjoint T)
    (hs : ρ (ιb j 1) * T = T) (y : BlockAlg d) :
    ContinuousLinearMap.adjoint (Jop ρ j o ζ) ∘L (T * ρ y * T) ∘L Jop ρ j o ζ
      = ((‖T ζ‖ ^ 2 : ℝ) : ℂ) • matCLM (d j) (y j) := by
  have hT1 : T * ρ (ιb j 1) = T := by rw [hcY, hs]
  have hy : ιb j 1 * y = ιb j (y j) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp [ιb]
    · simp [ιb, hk]
  have e1 : T * ρ y * T = ρ (ιb j (y j)) * (T * T) := by
    calc T * ρ y * T = T * ρ (ιb j 1) * ρ y * T := by rw [hT1]
      _ = T * ρ (ιb j (y j)) * T := by rw [mul_assoc T, ← map_mul, hy]
      _ = ρ (ιb j (y j)) * (T * T) := by rw [hcY, mul_assoc]
  have hQ : ∀ a b, T * T * Pu ρ j a b = Pu ρ j a b * (T * T) := fun a b => by
    rw [mul_assoc, Pu, hcY, ← mul_assoc, hcY, mul_assoc]
  rw [e1, J_sandwich ρ j o ζ hζ (T * T) hQ (y j)]
  congr 1
  rw [mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.star_eq_adjoint, hsa.star_eq, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

end Jop

end Cert.KitaevChannels
