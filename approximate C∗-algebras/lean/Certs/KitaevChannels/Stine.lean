import Certs.KitaevChannels.DeltaProps
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Lemma 12.4 in Stinespring form, on a Hilbert space of any dimension

`Δ(x) = W† ρ(x) W` (Stinespring). For block `j` and its unitary design `U_t`,
`R = ∑ₜ pₜ ρ(U_t†) W W† ρ(U_t)` commutes with `ρ(M_{dⱼ})` (the per-block diagonal identity) and is
self-adjoint. This replaces Kitaev's `R_j = 1 ⊗ C_j` (which uses `dim E_j < ∞` nowhere, but is
phrased with tensor factors).
-/

open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

section MatUnits

variable {d : ℕ}

theorem E_mul_E (a b c e : Fin d) : E a b * E c e = if b = c then E a e else 0 := by
  by_cases h : b = c
  · subst h
    rw [if_pos rfl]
    change CStarMatrix.ofMatrix (Matrix.single a b (1 : ℂ) * Matrix.single b e 1) = _
    rw [Matrix.single_mul_single_same, mul_one]; rfl
  · rw [if_neg h]
    change CStarMatrix.ofMatrix (Matrix.single a b (1 : ℂ) * Matrix.single c e 1) = 0
    rw [Matrix.single_mul_single_of_ne (c := (1 : ℂ)) a b c h (1 : ℂ)]; rfl

theorem star_E (a b : Fin d) : star (E a b) = E b a := by
  change CStarMatrix.ofMatrix (Matrix.conjTranspose (Matrix.single a b (1 : ℂ))) = _
  rw [Matrix.conjTranspose_single, star_one]; rfl

theorem E_Y_E (a b c e : Fin d) (Y : Mat d ℂ) : E a b * Y * E c e = Y b c • E a e := by
  change CStarMatrix.ofMatrix (Matrix.single a b (1 : ℂ) * (show Matrix (Fin d) (Fin d) ℂ from Y) *
    Matrix.single c e 1) = _
  rw [Matrix.single_mul_mul_single, one_mul, mul_one]
  refine CStarMatrix.ext fun i k => ?_
  change Matrix.single a e (Y b c) i k = Y b c * Matrix.single a e (1 : ℂ) i k
  simp [Matrix.single_apply]

end MatUnits

section Blocks

variable {m : ℕ} {d : Fin m → ℕ}

theorem ιb_mul (j : Fin m) (X Z : Mat (d j) ℂ) : ιb j (X * Z) = ιb j X * ιb j Z := by
  simp only [ιb, LinearMap.coe_single]
  exact Pi.single_mul (α := fun i => Mat (d i) ℂ) j X Z

theorem ιb_star (j : Fin m) (X : Mat (d j) ℂ) : ιb j (star X) = star (ιb j X) := by
  simp only [ιb, LinearMap.coe_single]
  exact Pi.single_star (f := fun i => Mat (d i) ℂ) j X

theorem norm_ιb (j : Fin m) (X : Mat (d j) ℂ) : ‖ιb (d := d) j X‖ = ‖X‖ := by
  simp only [ιb, LinearMap.coe_single]
  exact Pi.norm_single (G := fun i => Mat (d i) ℂ) X

end Blocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
  {m : ℕ} {d : Fin m → ℕ}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (ρ : BlockAlg d →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (j : Fin m) (Dj : Design (d j))

/-- `R = ∑ₜ pₜ ρ(ιⱼ(U_t†)) W W† ρ(ιⱼ(U_t))`. -/
def Rop : K →L[ℂ] K :=
  ∑ t, (Dj.p t : ℂ) • (ρ (ιb j (star (Dj.U t))) * (W ∘L ContinuousLinearMap.adjoint W)
    * ρ (ιb j (Dj.U t)))

/-- `R` commutes with `ρ(ιⱼ(Y))` (per-block diagonal identity). -/
theorem Rop_comm (Y : Mat (d j) ℂ) :
    Rop ρ W j Dj * ρ (ιb j Y) = ρ (ιb j Y) * Rop ρ W j Dj := by
  let β : Mat (d j) ℂ →ₗ[ℂ] Mat (d j) ℂ →ₗ[ℂ] (K →L[ℂ] K) :=
    LinearMap.mk₂ ℂ (fun X Z => ρ (ιb j X) * (W ∘L ContinuousLinearMap.adjoint W) * ρ (ιb j Z))
      (fun X X' Z => by simp only [map_add, add_mul])
      (fun c X Z => by simp only [map_smul, smul_mul_assoc])
      (fun X Z Z' => by simp only [map_add, mul_add])
      (fun c X Z => by simp only [map_smul, mul_smul_comm])
  have h := Dj.diag β Y
  simp only [β, LinearMap.mk₂_apply, ιb_mul, map_mul] at h
  unfold Rop
  rw [Finset.sum_mul, Finset.mul_sum]
  have e1 : ∀ t, (Dj.p t : ℂ) • (ρ (ιb j (star (Dj.U t))) * (W ∘L ContinuousLinearMap.adjoint W)
      * ρ (ιb j (Dj.U t))) * ρ (ιb j Y) = (Dj.p t : ℂ) • (ρ (ιb j (star (Dj.U t)))
      * (W ∘L ContinuousLinearMap.adjoint W) * (ρ (ιb j (Dj.U t)) * ρ (ιb j Y))) := fun t => by
    rw [smul_mul_assoc, mul_assoc]
  have e2 : ∀ t, ρ (ιb j Y) * ((Dj.p t : ℂ) • (ρ (ιb j (star (Dj.U t)))
      * (W ∘L ContinuousLinearMap.adjoint W) * ρ (ιb j (Dj.U t)))) = (Dj.p t : ℂ) •
      (ρ (ιb j Y) * ρ (ιb j (star (Dj.U t))) * (W ∘L ContinuousLinearMap.adjoint W)
      * ρ (ιb j (Dj.U t))) := fun t => by
    rw [mul_smul_comm, mul_assoc, mul_assoc, mul_assoc]
  simp only [e1, e2]
  exact h.symm

theorem Rop_isSelfAdjoint : IsSelfAdjoint (Rop ρ W j Dj) := by
  unfold Rop
  refine isSelfAdjoint_sum _ fun t _ => ?_
  have hWW : IsSelfAdjoint (W ∘L ContinuousLinearMap.adjoint W) := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  have hc : IsSelfAdjoint (Dj.p t : ℂ) := by
    rw [IsSelfAdjoint, RCLike.star_def, Complex.conj_ofReal]
  refine hc.smul ?_
  rw [IsSelfAdjoint, star_mul, star_mul, hWW.star_eq, ← map_star ρ (ιb j (Dj.U t)),
    ← map_star ρ (ιb j (star (Dj.U t))), ← ιb_star, ← ιb_star, star_star, mul_assoc]

theorem Rop_block_right : Rop ρ W j Dj * ρ (ιb j 1) = Rop ρ W j Dj := by
  unfold Rop
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_mul_assoc, mul_assoc, ← map_mul, ← ιb_mul, mul_one]

theorem Rop_block_left : ρ (ιb j 1) * Rop ρ W j Dj = Rop ρ W j Dj := by
  unfold Rop
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_smul_comm, ← mul_assoc, ← mul_assoc, ← map_mul, ← ιb_mul, one_mul]

end Cert.KitaevChannels
