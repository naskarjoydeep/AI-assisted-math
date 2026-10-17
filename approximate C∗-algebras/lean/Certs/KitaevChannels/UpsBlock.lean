import Certs.KitaevChannels.Zeta

/-!
# Kitaev's `Υ'_j` on a Hilbert space of any dimension, and `‖Υ'_j Δ - (·)_j‖_cb = O(η)`

Stinespring `Δ(x) = W† ρ(x) W`, `Φ(X) = V† π(X) V` (Kitaev uses the Choi form of `Φ`, which exists
only for normal `Φ`). With `B_s = W† ρ(ιⱼU_s) J` and `L = ∑ₛ pₛ π(Δ(ιⱼU_s†)) V B_s`,
`Υ'_j(X) = L† π(Φ(X)) L`. Kitaev's computation becomes two exact identities plus (12.34), (12.36).
-/

open scoped ComplexOrder InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

theorem starHom_adj {M K : Type} [CStarAlgebra M] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (x : M) :
    ContinuousLinearMap.adjoint (π x) = π (star x) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, map_star]

namespace Ctx

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
  (C : Ctx H)

set_option maxHeartbeats 1000000 in
/-- `Φ(Δ(a) Φ(Δ(y)) Δ(b)) ≈ Δ(a y b)` at every level: (12.34) and (12.36). -/
theorem sandwich_cb {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hK2 : ∀ (n : ℕ) (X' Y' Z' : Mat n (H →L[ℂ] H)),
      ‖(((X'.map C.Φ * Y'.map C.Φ).map C.Φ) * Z'.map C.Φ).map C.Φ
        - (X'.map C.Φ * Y'.map C.Φ * Z'.map C.Φ).map C.Φ‖ ≤ c₂ * C.η * ‖X'‖ * ‖Y'‖ * ‖Z'‖)
    (a b : BlockAlg C.d) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    CBBound (C.Φ.toLinearMap ∘ₗ lrMul (C.Δ a) (C.Δ b) ∘ₗ C.Φ.toLinearMap ∘ₗ C.Δ
      - C.Δ ∘ₗ lrMul a b) (C.e34 + C.e36 c₂) := by
  intro n Y
  rw [amp_sub_fun, amp_comp, amp_comp, amp_comp, amp_comp, amp_lrMul, amp_lrMul,
    ← amp_diagM n C.Δ a, ← amp_diagM n C.Δ b]
  set A := diagM n a
  set B := diagM n b
  have hA : ‖A‖ ≤ 1 := (norm_diagM_le n a).trans ha
  have hB : ‖B‖ ≤ 1 := (norm_diagM_le n b).trans hb
  have hAn := norm_nonneg A
  have hBn := norm_nonneg B
  have hYn := norm_nonneg Y
  set a' := A.map C.Δ
  set b' := B.map C.Δ
  set y' := Y.map C.Δ
  have ha' : ‖a'‖ ≤ 1 := by have h := C.delta_cb n A; rw [one_mul] at h; exact h.trans hA
  have hb' : ‖b'‖ ≤ 1 := by have h := C.delta_cb n B; rw [one_mul] at h; exact h.trans hB
  have hd : ‖y'.map C.Φ.toLinearMap - y'‖ ≤ C.e34 * ‖Y‖ := by
    have := C.phi_delta_cb n Y; rwa [amp_sub_fun, amp_comp] at this
  have h1 : ‖(a' * y'.map C.Φ.toLinearMap * b').map C.Φ.toLinearMap
      - (a' * y' * b').map C.Φ.toLinearMap‖ ≤ C.e34 * ‖Y‖ := by
    rw [← amp_sub, ← sub_mul, ← mul_sub]
    have h := C.phi_cb n (a' * (y'.map C.Φ.toLinearMap - y') * b')
    rw [one_mul] at h
    refine h.trans ?_
    set D := y'.map C.Φ.toLinearMap - y'
    have k1 : ‖a' * D * b'‖ ≤ ‖a' * D‖ * ‖b'‖ := norm_mul_le (a' * D) b'
    have k2 : ‖a' * D‖ ≤ ‖a'‖ * ‖D‖ := norm_mul_le a' D
    have k3 := norm_nonneg D
    have k4 := norm_nonneg (a' * D)
    have k5 := norm_nonneg a'
    have k6 := norm_nonneg b'
    have k7 := C.e34_nonneg
    generalize ‖a' * D * b'‖ = t1 at *
    generalize ‖a' * D‖ = t2 at *
    generalize ‖D‖ = t3 at *
    generalize ‖a'‖ = t4 at *
    generalize ‖b'‖ = t5 at *
    generalize ‖Y‖ = t6 at *
    have : t2 ≤ C.e34 * t6 := k2.trans (by nlinarith)
    nlinarith
  have h2 := C.mul36 hc₂ (hK2 n) A Y B
  have h3 : C.e36 c₂ * ‖A‖ * ‖Y‖ * ‖B‖ ≤ C.e36 c₂ * ‖Y‖ := by
    have he36 : 0 ≤ C.e36 c₂ := by
      have := C.e34_nonneg; have := C.e35_nonneg; have := C.hη; unfold e36; positivity
    have : ‖A‖ * ‖B‖ ≤ 1 := by nlinarith
    nlinarith [mul_nonneg he36 hYn]
  calc ‖(a' * y'.map C.Φ.toLinearMap * b').map C.Φ.toLinearMap - (A * Y * B).map C.Δ‖
      ≤ ‖(a' * y'.map C.Φ.toLinearMap * b').map C.Φ.toLinearMap
          - (a' * y' * b').map C.Φ.toLinearMap‖
        + ‖(a' * y' * b').map C.Φ.toLinearMap - (A * Y * B).map C.Δ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C.e34 * ‖Y‖ + C.e36 c₂ * ‖Y‖ := add_le_add h1 (h2.trans h3)
    _ = (C.e34 + C.e36 c₂) * ‖Y‖ := by ring

end Ctx

section Kitaev

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
  (C : Ctx H)
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (ρ : BlockAlg C.d →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K)
  {K' : Type} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  (π : (H →L[ℂ] H) →⋆ₐ[ℂ] (K' →L[ℂ] K')) (V : H →L[ℂ] K')
  (j : Fin C.m) (Dj : Design (C.d j)) (o : Fin (C.d j)) (ζ : K)

local notation "Eu" => EuclideanSpace ℂ (Fin (C.d j))

/-- `B_s = W† ρ(ιⱼ U_s) J` (Kitaev's `W_j† (U_s ⊗ ξ_j)`). -/
def Bop (s : Dj.S) : Eu →L[ℂ] H :=
  ContinuousLinearMap.adjoint W ∘L ρ (ιb j (Dj.U s)) ∘L Jop ρ j o ζ

/-- Kitaev's `L_j = ∑ₛ pₛ π(Δ(U_s†)) V B_s`. -/
def Lop : Eu →L[ℂ] K' :=
  ∑ s, (Dj.p s : ℂ) • (π (C.Δ (ιb j (star (Dj.U s)))) ∘L V ∘L Bop C ρ W j Dj o ζ s)

/-- `x ↦ A† x B` on `B(H)`. -/
abbrev lr {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A B : E →L[ℂ] H) : (H →L[ℂ] H) →ₗ[ℂ] (E →L[ℂ] E) :=
  compress (StarAlgHom.id ℂ (H →L[ℂ] H)) A B

theorem Delta_star (x : BlockAlg C.d) : C.Δ (star x) = star (C.Δ x) :=
  star_of_cp C.hF C.hΔ.2 x

/-- **First identity**: `L† π(Z) L = ∑ᵣₛ pᵣpₛ B_r† Φ(Δ(U_r) Z Δ(U_s†)) B_s`. -/
theorem compress_L (hV : ∀ x, C.Φ x = ContinuousLinearMap.adjoint V ∘L π x ∘L V) (Z : H →L[ℂ] H) :
    compress π (Lop C ρ W π V j Dj o ζ) (Lop C ρ W π V j Dj o ζ) Z
      = ∑ r, ∑ s, ((Dj.p r * Dj.p s : ℝ) : ℂ) • lr (Bop C ρ W j Dj o ζ r) (Bop C ρ W j Dj o ζ s)
          (C.Φ (C.Δ (ιb j (Dj.U r)) * Z * C.Δ (ιb j (star (Dj.U s))))) := by
  have hLadj : ContinuousLinearMap.adjoint (Lop C ρ W π V j Dj o ζ) = ∑ r, (Dj.p r : ℂ) •
      (ContinuousLinearMap.adjoint (Bop C ρ W j Dj o ζ r) ∘L ContinuousLinearMap.adjoint V
        ∘L π (C.Δ (ιb j (Dj.U r)))) := by
    rw [Lop, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smulₛₗ, Complex.conj_ofReal, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, starHom_adj, ← Delta_star, ← ιb_star, star_star,
      ContinuousLinearMap.comp_assoc]
  rw [compress_apply, hLadj]
  conv_lhs => rw [Lop]
  rw [ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ContinuousLinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [compress_apply, hV, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, Complex.ofReal_mul, mul_comm (Dj.p r : ℂ)]
  congr 1
  rw [map_mul π, map_mul π]
  simp only [StarAlgHom.coe_id, id_eq, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc]

/-- **Second identity**: `∑ᵣₛ pᵣpₛ B_r† Δ(U_r y U_s†) B_s = ‖Rζ‖² y_j` (Kitaev's last three lines). -/
theorem Delta_sum (hW : ∀ x, C.Δ x = ContinuousLinearMap.adjoint W ∘L ρ x ∘L W)
    (hζ : Pu ρ j o o ζ = ζ) (y : BlockAlg C.d) :
    ∑ r, ∑ s, ((Dj.p r * Dj.p s : ℝ) : ℂ) • lr (Bop C ρ W j Dj o ζ r) (Bop C ρ W j Dj o ζ s)
        (C.Δ (ιb j (Dj.U r) * y * ιb j (star (Dj.U s))))
      = ((‖Rop ρ W j Dj ζ‖ ^ 2 : ℝ) : ℂ) • matCLM (C.d j) (y j) := by
  refine Eq.trans ?_ (T_sandwich ρ j o ζ hζ (Rop ρ W j Dj) (fun Y => Rop_comm ρ W j Dj Y)
    (Rop_isSelfAdjoint ρ W j Dj) (Rop_block_left ρ W j Dj) y)
  unfold Rop
  rw [Finset.sum_mul, Finset.sum_mul, ContinuousLinearMap.finsetSum_comp,
    ContinuousLinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum, ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, Complex.ofReal_mul]
  congr 1
  rw [compress_apply, hW, Bop, Bop, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, rho_adj, ← ιb_star,
    map_mul ρ, map_mul ρ]
  simp only [StarAlgHom.coe_id, id_eq, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc]

/-- The difference maps `D_rs = Φ ∘ (Δ(U_r) · Δ(U_s†)) ∘ Φ ∘ Δ - Δ ∘ (U_r · U_s†)`. -/
abbrev Dmap (a b : BlockAlg C.d) : BlockAlg C.d →ₗ[ℂ] (H →L[ℂ] H) :=
  C.Φ.toLinearMap ∘ₗ lrMul (C.Δ a) (C.Δ b) ∘ₗ C.Φ.toLinearMap ∘ₗ C.Δ - C.Δ ∘ₗ lrMul a b

/-- `Υ'_j Δ - ‖Rζ‖² (·)_j = ∑ᵣₛ pᵣpₛ (B_r† · B_s) ∘ D_rs`, as linear maps. -/
theorem ups_delta_eq (hW : ∀ x, C.Δ x = ContinuousLinearMap.adjoint W ∘L ρ x ∘L W)
    (hV : ∀ x, C.Φ x = ContinuousLinearMap.adjoint V ∘L π x ∘L V) (hζ : Pu ρ j o o ζ = ζ) :
    toMat (compress π (Lop C ρ W π V j Dj o ζ) (Lop C ρ W π V j Dj o ζ) ∘ₗ C.Φ.toLinearMap)
        ∘ₗ C.Δ - ((‖Rop ρ W j Dj ζ‖ ^ 2 : ℝ) : ℂ) • LinearMap.proj j
      = ∑ r, ∑ s, ((Dj.p r * Dj.p s : ℝ) : ℂ) • toMat (lr (Bop C ρ W j Dj o ζ r)
          (Bop C ρ W j Dj o ζ s) ∘ₗ Dmap C (ιb j (Dj.U r)) (ιb j (star (Dj.U s)))) := by
  refine LinearMap.ext fun y => ?_
  have e1 : (toMat (compress π (Lop C ρ W π V j Dj o ζ) (Lop C ρ W π V j Dj o ζ)
      ∘ₗ C.Φ.toLinearMap) ∘ₗ C.Δ) y = (matCLM (C.d j)).symm (∑ r, ∑ s,
        ((Dj.p r * Dj.p s : ℝ) : ℂ) • lr (Bop C ρ W j Dj o ζ r) (Bop C ρ W j Dj o ζ s)
          (C.Φ (C.Δ (ιb j (Dj.U r)) * C.Φ (C.Δ y) * C.Δ (ιb j (star (Dj.U s)))))) := by
    rw [LinearMap.comp_apply, toMat_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      compress_L C ρ W π V j Dj o ζ hV]
  have e2 : y j = (matCLM (C.d j)).symm (matCLM (C.d j) (y j)) :=
    ((matCLM (C.d j)).symm_apply_apply _).symm
  rw [LinearMap.sub_apply, e1, LinearMap.smul_apply, LinearMap.proj_apply, e2, ← map_smul,
    ← Delta_sum C ρ W j Dj o ζ hW hζ y, ← map_sub, ← Finset.sum_sub_distrib, map_sum,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_sub_distrib, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_sub, map_smul, map_smul, ← smul_sub, LinearMap.smul_apply]
  congr 1
  rw [toMat_apply, LinearMap.comp_apply, LinearMap.sub_apply, map_sub, map_sub]
  rfl

theorem norm_Bop_le (hW : ∀ x, C.Δ x = ContinuousLinearMap.adjoint W ∘L ρ x ∘L W)
    (hζ : Pu ρ j o o ζ = ζ) (hζn : ‖ζ‖ ≤ 1) (s : Dj.S) : ‖Bop C ρ W j Dj o ζ s‖ ≤ 1 := by
  have h1 := Wadj_norm_le C ρ W hW
  have h2 : ‖ρ (ιb j (Dj.U s))‖ ≤ 1 := (norm_rho_le ρ _).trans (by
    rw [norm_ιb]; exact norm_le_one_of_star_mul_self (Dj.unit s).1)
  have h3 := norm_J_le ρ j o ζ hζ hζn
  calc ‖Bop C ρ W j Dj o ζ s‖
      ≤ ‖ContinuousLinearMap.adjoint W‖ * ‖ρ (ιb j (Dj.U s)) ∘L Jop ρ j o ζ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (1 * 1) := by
        refine mul_le_mul h1 ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul h2 h3 (norm_nonneg _) zero_le_one)) (norm_nonneg _) zero_le_one
    _ = 1 := by ring

theorem norm_le_one_of_adj_comp {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) (h : ContinuousLinearMap.adjoint A ∘L A = 1) : ‖A‖ ≤ 1 := by
  have h2 := ContinuousLinearMap.norm_adjoint_comp_self A
  rw [h] at h2
  have h3 : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := norm_one_le_one'
  nlinarith [norm_nonneg A]

theorem norm_Lop_le (hW : ∀ x, C.Δ x = ContinuousLinearMap.adjoint W ∘L ρ x ∘L W)
    (hV : ∀ x, C.Φ x = ContinuousLinearMap.adjoint V ∘L π x ∘L V)
    (hζ : Pu ρ j o o ζ = ζ) (hζn : ‖ζ‖ ≤ 1) : ‖Lop C ρ W π V j Dj o ζ‖ ≤ 1 := by
  have hVn : ‖V‖ ≤ 1 := by
    refine norm_le_one_of_adj_comp V ?_
    have := hV 1
    rw [show C.Φ 1 = 1 from C.hΦ.1, map_one,
      show (1 : K' →L[ℂ] K') = ContinuousLinearMap.id ℂ K' from rfl,
      ContinuousLinearMap.id_comp] at this
    exact this.symm
  have hterm : ∀ s, ‖(Dj.p s : ℂ) • (π (C.Δ (ιb j (star (Dj.U s)))) ∘L V
      ∘L Bop C ρ W j Dj o ζ s)‖ ≤ Dj.p s := fun s => by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Dj.p_nonneg s)]
    refine mul_le_of_le_one_right (Dj.p_nonneg s) ?_
    have hπ : ‖π (C.Δ (ιb j (star (Dj.U s))))‖ ≤ 1 := by
      refine (NonUnitalStarAlgHom.norm_apply_le π _).trans ?_
      have h := C.delta_cb.apply_le (ιb j (star (Dj.U s)))
      refine h.trans ?_
      rw [one_mul, norm_ιb]
      exact norm_le_one_of_star_mul_self (by rw [star_star]; exact (Dj.unit s).2)
    have hB := norm_Bop_le C ρ W j Dj o ζ hW hζ hζn s
    calc ‖π (C.Δ (ιb j (star (Dj.U s)))) ∘L V ∘L Bop C ρ W j Dj o ζ s‖
        ≤ ‖π (C.Δ (ιb j (star (Dj.U s))))‖ * ‖V ∘L Bop C ρ W j Dj o ζ s‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (1 * 1) := by
          refine mul_le_mul hπ ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul hVn hB (norm_nonneg _) zero_le_one)) (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  calc ‖Lop C ρ W π V j Dj o ζ‖ ≤ ∑ s, Dj.p s := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun s _ => hterm s)
    _ = 1 := Dj.p_sum

theorem Rop_norm_le (hW : ∀ x, C.Δ x = ContinuousLinearMap.adjoint W ∘L ρ x ∘L W) :
    ‖Rop ρ W j Dj‖ ≤ 1 := by
  have hWW : ‖W ∘L ContinuousLinearMap.adjoint W‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      have := W_norm_le C ρ W hW; have := Wadj_norm_le C ρ W hW
      nlinarith [norm_nonneg W, norm_nonneg (ContinuousLinearMap.adjoint W)])
  have hterm : ∀ t, ‖(Dj.p t : ℂ) • (ρ (ιb j (star (Dj.U t))) * (W ∘L ContinuousLinearMap.adjoint W)
      * ρ (ιb j (Dj.U t)))‖ ≤ Dj.p t := fun t => by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Dj.p_nonneg t)]
    refine mul_le_of_le_one_right (Dj.p_nonneg t) ?_
    have h1 : ‖ρ (ιb j (star (Dj.U t)))‖ ≤ 1 := (norm_rho_le ρ _).trans (by
      rw [norm_ιb]; exact norm_le_one_of_star_mul_self (by rw [star_star]; exact (Dj.unit t).2))
    have h2 : ‖ρ (ιb j (Dj.U t))‖ ≤ 1 := (norm_rho_le ρ _).trans (by
      rw [norm_ιb]; exact norm_le_one_of_star_mul_self (Dj.unit t).1)
    refine (norm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
    have := norm_nonneg (ρ (ιb j (star (Dj.U t))))
    have := norm_nonneg (W ∘L ContinuousLinearMap.adjoint W)
    have := norm_nonneg (ρ (ιb j (Dj.U t)))
    calc ‖ρ (ιb j (star (Dj.U t)))‖ * ‖W ∘L ContinuousLinearMap.adjoint W‖ * ‖ρ (ιb j (Dj.U t))‖
        ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  unfold Rop
  calc _ ≤ ∑ t, Dj.p t := (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => hterm t)
    _ = 1 := Dj.p_sum

end Kitaev

section BlockBound

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
  (C : Ctx H)
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (ρ : BlockAlg C.d →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K)
  {K' : Type} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  (π : (H →L[ℂ] H) →⋆ₐ[ℂ] (K' →L[ℂ] K')) (V : H →L[ℂ] K')

theorem cb_proj (j : Fin C.m) :
    CBBound (LinearMap.proj (R := ℂ) (φ := fun j => Mat (C.d j) ℂ) j) 1 := fun n X => by
  rw [one_mul]; exact norm_block_le n X j

set_option maxHeartbeats 1000000 in
/-- **Per-block estimate.** For each block there is `L` with `‖L‖ ≤ 1` and
`‖Υ'_j Δ - (·)_j‖_cb ≤ 4(e34 + e36) + 2(δ + e + e35 + τ)`, where `Υ'_j = L† π(Φ(·)) L`. -/
theorem block_bound (hS : StinespringThm)
    (hW : ∀ x, C.Δ x = ContinuousLinearMap.adjoint W ∘L ρ x ∘L W)
    (hV : ∀ x, C.Φ x = ContinuousLinearMap.adjoint V ∘L π x ∘L V)
    {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hK2 : ∀ (n : ℕ) (X' Y' Z' : Mat n (H →L[ℂ] H)),
      ‖(((X'.map C.Φ * Y'.map C.Φ).map C.Φ) * Z'.map C.Φ).map C.Φ
        - (X'.map C.Φ * Y'.map C.Φ * Z'.map C.Φ).map C.Φ‖ ≤ c₂ * C.η * ‖X'‖ * ‖Y'‖ * ‖Z'‖)
    (j : Fin C.m) (Dj : Design (C.d j)) {τ : ℝ} (hτ : 0 < τ) :
    ∃ L : EuclideanSpace ℂ (Fin (C.d j)) →L[ℂ] K', ‖L‖ ≤ 1 ∧
      CBBound (toMat (compress π L L ∘ₗ C.Φ.toLinearMap) ∘ₗ C.Δ - LinearMap.proj j)
        (4 * (C.e34 + C.e36 c₂) + 2 * (C.δ + C.e + C.e35 + τ)) := by
  have hk : 0 ≤ C.e34 + C.e36 c₂ := by
    have := C.e34_nonneg; have := C.e35_nonneg; have := C.hη; unfold Ctx.e36; positivity
  have hg : 0 ≤ C.δ + C.e + C.e35 + τ := by
    have := C.e35_nonneg; have := C.hδ; have := C.he; positivity
  by_cases hdj : 0 < C.d j
  swap
  · refine ⟨0, by rw [norm_zero]; exact zero_le_one, fun n X => ?_⟩
    have h0 : X.map (toMat (compress π (0 : EuclideanSpace ℂ (Fin (C.d j)) →L[ℂ] K') 0
        ∘ₗ C.Φ.toLinearMap) ∘ₗ C.Δ - LinearMap.proj (R := ℂ) (φ := fun j => Mat (C.d j) ℂ) j)
        = (0 : Mat n (Mat (C.d j) ℂ)) :=
      CStarMatrix.ext fun i k => CStarMatrix.ext fun (a : Fin (C.d j)) b => absurd a.isLt (by omega)
    rw [h0, norm_zero]
    have := norm_nonneg X
    positivity
  set o : Fin (C.d j) := ⟨0, hdj⟩
  set R := Rop ρ W j Dj
  obtain ⟨ζ, hζ, hζn, hRζ⟩ := exists_zeta ρ j o R (fun a b => Rop_comm ρ W j Dj _)
    (Rop_block_left ρ W j Dj) hτ
  refine ⟨Lop C ρ W π V j Dj o ζ, norm_Lop_le C ρ W π V j Dj o ζ hW hV hζ hζn, ?_⟩
  have heq := ups_delta_eq C ρ W π V j Dj o ζ hW hV hζ
  set c : ℂ := ((‖R ζ‖ ^ 2 : ℝ) : ℂ) with hc
  have hsplit : toMat (compress π (Lop C ρ W π V j Dj o ζ) (Lop C ρ W π V j Dj o ζ)
      ∘ₗ C.Φ.toLinearMap) ∘ₗ C.Δ - LinearMap.proj j
      = (toMat (compress π (Lop C ρ W π V j Dj o ζ) (Lop C ρ W π V j Dj o ζ)
        ∘ₗ C.Φ.toLinearMap) ∘ₗ C.Δ - c • LinearMap.proj j) + (c - 1) • LinearMap.proj j := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, sub_smul, one_smul]
    abel
  rw [hsplit, heq]
  have hterm : ∀ r s, CBBound (toMat (lr (Bop C ρ W j Dj o ζ r) (Bop C ρ W j Dj o ζ s)
      ∘ₗ Dmap C (ιb j (Dj.U r)) (ιb j (star (Dj.U s))))) (4 * (C.e34 + C.e36 c₂)) := fun r s => by
    have h1 := compress_cb C.hF hS (StarAlgHom.id ℂ (H →L[ℂ] H)) (Bop C ρ W j Dj o ζ r)
      (Bop C ρ W j Dj o ζ s)
    have h2 := C.sandwich_cb hc₂ hK2 (ιb j (Dj.U r)) (ιb j (star (Dj.U s)))
      (by rw [norm_ιb]; exact norm_le_one_of_star_mul_self (Dj.unit r).1)
      (by rw [norm_ιb]; exact norm_le_one_of_star_mul_self (by rw [star_star]; exact (Dj.unit s).2))
    refine (toMat_cb (h1.comp (by positivity) h2)).mono ?_
    have hr := norm_Bop_le C ρ W j Dj o ζ hW hζ hζn r
    have hs := norm_Bop_le C ρ W j Dj o ζ hW hζ hζn s
    have := norm_nonneg (Bop C ρ W j Dj o ζ r)
    have := norm_nonneg (Bop C ρ W j Dj o ζ s)
    have : (‖Bop C ρ W j Dj o ζ r‖ + ‖Bop C ρ W j Dj o ζ s‖) ^ 2 ≤ 4 := by nlinarith
    nlinarith
  have hsum := CBBound.sum Finset.univ _ _ fun r _ => CBBound.sum Finset.univ _ _ fun s _ =>
    (hterm r s).smul ((Dj.p r * Dj.p s : ℝ) : ℂ)
  have hnum : ∑ r, ∑ s, ‖((Dj.p r * Dj.p s : ℝ) : ℂ)‖ * (4 * (C.e34 + C.e36 c₂))
      = 4 * (C.e34 + C.e36 c₂) := by
    have e : ∀ r s, ‖((Dj.p r * Dj.p s : ℝ) : ℂ)‖ * (4 * (C.e34 + C.e36 c₂))
        = Dj.p r * (Dj.p s * (4 * (C.e34 + C.e36 c₂))) := fun r s => by
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Dj.p_nonneg r) (Dj.p_nonneg s))]
      ring
    simp_rw [e, ← Finset.mul_sum, ← Finset.sum_mul, Dj.p_sum, one_mul]
  rw [hnum] at hsum
  have hnorm : ‖c - 1‖ ≤ 2 * (C.δ + C.e + C.e35 + τ) := by
    have hlow := Rop_norm_ge C ρ W hW j Dj hdj
    have hRle := Rop_norm_le C ρ W j Dj hW
    have hup : ‖R ζ‖ ≤ 1 := (R.le_opNorm ζ).trans (by
      have := norm_nonneg R; have := norm_nonneg ζ; nlinarith)
    have hr0 := norm_nonneg (R ζ)
    rw [hc, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_le]
    constructor <;> nlinarith
  refine (hsum.add ((cb_proj C j).smul (c - 1))).mono ?_
  linarith

end BlockBound

end Cert.KitaevChannels
