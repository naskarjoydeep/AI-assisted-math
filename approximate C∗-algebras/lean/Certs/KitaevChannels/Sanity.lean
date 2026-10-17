import Certs.KitaevChannels.Proof
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Non-vacuity: the hypotheses of `Claim` hold on an infinite-dimensional Hilbert space

On `ℓ²(ℕ)` the map `Φ(X) = ⟨e₀, X e₀⟩ · 1` (measure the pure state `e₀`, reprepare `1`) is UCP,
exactly idempotent, and `Φ̃ = Φ` has rank one. So `Claim` really applies to an infinite-dimensional
`H` with a finite-dimensional logical algebra, which is Theorem A's setting. Complete positivity is
proved from scratch: `Φₙ(Y†Y) = ∑ₖ G(Yₖ·e₀) ⊗ 1` with `G` a Gram matrix, and a positive semidefinite
scalar matrix tensored with `1` is a sum of `Z†Z`.
-/

open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace Cert.KitaevChannels

section State

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `Φ(X) = ⟨ψ, X ψ⟩ · 1`. -/
def statePhi (ψ : H) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ((innerSL ℂ ψ).comp (ContinuousLinearMap.apply ℂ H ψ)).smulRight (1 : H →L[ℂ] H)

theorem statePhi_apply (ψ : H) (X : H →L[ℂ] H) :
    statePhi ψ X = ⟪ψ, X ψ⟫_ℂ • (1 : H →L[ℂ] H) := rfl

/-- A Gram matrix tensored with `1` is positive in `Mₙ(B(H))`. -/
theorem gram_one_nonneg {n : ℕ} (v : Fin n → H) :
    0 ≤ (CStarMatrix.ofMatrix (fun a b => ⟪v a, v b⟫_ℂ • (1 : H →L[ℂ] H)) : Mat n (H →L[ℂ] H)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : (CStarMatrix.ofMatrix (fun a b => ⟪v a, v b⟫_ℂ • (1 : H →L[ℂ] H)) :
        Mat 0 (H →L[ℂ] H)) = 0 := CStarMatrix.ext fun a => Fin.elim0 a
    rw [this]
  obtain ⟨m, w, hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 (Matrix.posSemidef_gram ℂ v)
  let o : Fin n := ⟨0, hn⟩
  let Z : Fin m → Mat n (H →L[ℂ] H) := fun i =>
    CStarMatrix.ofMatrix fun l b => if l = o then star (w i b) • (1 : H →L[ℂ] H) else 0
  have key : (CStarMatrix.ofMatrix (fun a b => ⟪v a, v b⟫_ℂ • (1 : H →L[ℂ] H)) : Mat n _)
      = ∑ i, star (Z i) * Z i := by
    refine CStarMatrix.ext fun a b => ?_
    have hab : ⟪v a, v b⟫_ℂ = ∑ i, w i a * star (w i b) := by
      have := congrFun (congrFun hw a) b
      simpa [Matrix.gram, Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    rw [cm_sum_apply]
    change ⟪v a, v b⟫_ℂ • (1 : H →L[ℂ] H) = ∑ i, (star (Z i) * Z i) a b
    rw [hab, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [CStarMatrix.mul_apply, Finset.sum_eq_single o]
    · rw [CStarMatrix.star_apply]
      change (w i a * star (w i b)) • (1 : H →L[ℂ] H)
        = star (if o = o then star (w i a) • (1 : H →L[ℂ] H) else 0)
          * (if o = o then star (w i b) • (1 : H →L[ℂ] H) else 0)
      rw [if_pos rfl, if_pos rfl, star_smul, star_star, star_one, smul_mul_smul_comm, one_mul]
    · intro l _ hl
      rw [CStarMatrix.star_apply]
      change star (if l = o then star (w i a) • (1 : H →L[ℂ] H) else 0)
        * (if l = o then star (w i b) • (1 : H →L[ℂ] H) else 0) = 0
      rw [if_neg hl, if_neg hl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ o) h
  rw [key]
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg (Z i)

theorem statePhi_cp (ψ : H) : IsCP (statePhi ψ).toLinearMap := by
  intro n X hX
  rw [StarOrderedRing.nonneg_iff] at hX
  induction hX using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨Y, rfl⟩ := hx
    have key : (star Y * Y).map (statePhi ψ).toLinearMap = ∑ k,
        (CStarMatrix.ofMatrix (fun a b => ⟪Y k a ψ, Y k b ψ⟫_ℂ • (1 : H →L[ℂ] H)) :
          Mat n (H →L[ℂ] H)) := by
      refine CStarMatrix.ext fun a b => ?_
      rw [amp_apply, cm_sum_apply, CStarMatrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [CStarMatrix.star_apply, ContinuousLinearMap.coe_coe, statePhi_apply, mul_apply_eq_comp,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      rfl
    rw [key]
    exact Finset.sum_nonneg fun k _ => gram_one_nonneg (fun b => Y k b ψ)
  | zero =>
    rw [show (0 : Mat n (H →L[ℂ] H)).map (statePhi ψ).toLinearMap = 0 from
      CStarMatrix.ext fun i j => map_zero (statePhi ψ).toLinearMap]
  | add x y _ _ hx hy => rw [amp_add]; exact add_nonneg hx hy

variable {ψ : H} (hψ : ⟪ψ, ψ⟫_ℂ = 1)
include hψ

theorem statePhi_one : statePhi ψ 1 = 1 := by
  rw [statePhi_apply, show (1 : H →L[ℂ] H) ψ = ψ from rfl, hψ, one_smul]

theorem statePhi_idem : statePhi ψ * statePhi ψ = statePhi ψ := by
  refine ContinuousLinearMap.ext fun X => ?_
  rw [mul_apply_eq_comp, statePhi_apply ψ X, map_smul, statePhi_one hψ]

end State

set_option synthInstance.maxHeartbeats 400000 in
/-- If `Φ² = Φ` then `Φ̃ = Φ`. -/
theorem tildePhi_of_idem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)} (h : Φ * Φ = Φ) : tildePhi Φ = Φ := by
  unfold tildePhi
  rw [h, sub_self, smul_zero]
  have hs : (∑' k : ℕ, ((Nat.centralBinom k : ℂ) / 4 ^ k) •
      (0 : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) ^ k) = 1 := by
    rw [tsum_eq_single 0 (fun k hk => by
      rw [zero_pow hk]; exact ContinuousLinearMap.ext fun x => by simp)]
    simp
  rw [hs, mul_one, add_sub_cancel, two_nsmul, ← two_smul ℂ, smul_smul]
  norm_num

/-- ℓ²(ℕ) is infinite-dimensional. -/
theorem l2_not_finiteDimensional : ¬ FiniteDimensional ℂ (lp (fun _ : ℕ => ℂ) 2) := by
  intro hfin
  let e : ℕ → lp (fun _ : ℕ => ℂ) 2 := fun n => lp.single 2 n 1
  let coe : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] (ℕ → ℂ) :=
    { toFun := fun f => (f : ℕ → ℂ), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hli : LinearIndependent ℂ (coe ∘ e) := by
    have : coe ∘ e = fun n => Pi.single n (1 : ℂ) := by
      funext n
      rfl
    rw [this]
    exact Pi.linearIndependent_single_one ℕ ℂ
  have : Finite ℕ := (LinearIndependent.of_comp coe hli).finite_of_isNoetherian
  exact (Infinite.not_finite this).elim

/-- **Non-vacuity.** On the infinite-dimensional Hilbert space `ℓ²(ℕ)` there is a UCP map with
`‖Φ² - Φ‖_cb ≤ η` for every `η ≥ 0` and `Φ̃` of finite rank: every hypothesis of `Claim` on
`(H, Φ, η)` holds (with `η = 0 < η₀`). -/
theorem hyps_satisfiable_infinite_dim :
    Nontrivial (lp (fun _ : ℕ => ℂ) 2) ∧ ¬ FiniteDimensional ℂ (lp (fun _ : ℕ => ℂ) 2) ∧
    ∃ Φ : (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) →L[ℂ]
        (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2),
      IsUCP Φ.toLinearMap ∧ (∀ η : ℝ, 0 ≤ η → CBBound (Φ * Φ - Φ).toLinearMap η) ∧
      FiniteDimensional ℂ (LinearMap.range (tildePhi Φ).toLinearMap) := by
  set ψ : lp (fun _ : ℕ => ℂ) 2 := lp.single 2 0 1
  have hψn : ‖ψ‖ = 1 := by rw [lp.norm_single (by norm_num), norm_one]
  have hψ : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψn]; norm_num
  have hntr : Nontrivial (lp (fun _ : ℕ => ℂ) 2) := ⟨⟨ψ, 0, fun h => by
    rw [h, norm_zero] at hψn; exact zero_ne_one hψn⟩⟩
  refine ⟨hntr, l2_not_finiteDimensional, statePhi ψ, ⟨statePhi_one hψ, statePhi_cp ψ⟩,
    fun η hη => ?_, ?_⟩
  · rw [statePhi_idem hψ, show statePhi ψ - statePhi ψ = 0 from sub_self _,
      ContinuousLinearMap.toLinearMap_zero]
    exact (CBBound.zero).mono hη
  · rw [tildePhi_of_idem (statePhi_idem hψ)]
    have hle : LinearMap.range (statePhi ψ).toLinearMap
        ≤ Submodule.span ℂ {(1 : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)} := by
      rintro _ ⟨X, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    exact Submodule.finiteDimensional_of_le hle

end Cert.KitaevChannels
