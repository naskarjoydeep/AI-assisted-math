import Certs.KitaevChannels.Toolkit
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Plumbing: compressions, block algebras, and matrices as operators

* `compress π A B : x ↦ A† π(x) B`, its complete positivity (`A = B`, Stinespring's easy
  direction) and its cb-bound `(‖A‖ + ‖B‖)²` (polarization + `‖φ‖_cb = ‖φ(1)‖`).
* `blockMatEquiv : Mₙ(⊕ⱼ M_{dⱼ}) ≃⋆ₐ ⊕ⱼ Mₙ(M_{dⱼ})`, used to check positivity and norms of
  block-algebra-valued maps one block at a time.
* `matCLM : M_d(ℂ) ≃⋆ₐ B(ℂ^d)`.
-/

open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

section Facts

variable (hF : CPMapFacts)
include hF

theorem cb_of_cp {M₁ M₂ : Type} [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
    [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂] {φ : M₁ →ₗ[ℂ] M₂} (h : IsCP φ) :
    CBBound φ ‖φ 1‖ := (hF M₁ M₂ φ h).1

theorem star_of_cp {M₁ M₂ : Type} [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
    [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂] {φ : M₁ →ₗ[ℂ] M₂} (h : IsCP φ)
    (x : M₁) : φ (star x) = star (φ x) := (hF M₁ M₂ φ h).2 x

theorem cb_of_ucp {M₁ M₂ : Type} [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
    [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂] [Nontrivial M₂] {φ : M₁ →ₗ[ℂ] M₂}
    (h : IsUCP φ) : CBBound φ 1 := by
  have := cb_of_cp hF h.2
  rwa [h.1, norm_one] at this

end Facts

section Compress

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {M : Type} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- `x ↦ A† π(x) B`. -/
def compress (π : M →⋆ₐ[ℂ] (F →L[ℂ] F)) (A B : E →L[ℂ] F) : M →ₗ[ℂ] (E →L[ℂ] E) where
  toFun x := (ContinuousLinearMap.adjoint A) ∘L π x ∘L B
  map_add' x y := by
    rw [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' c x := by
    rw [map_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]; rfl

theorem compress_apply (π : M →⋆ₐ[ℂ] (F →L[ℂ] F)) (A B : E →L[ℂ] F) (x : M) :
    compress π A B x = (ContinuousLinearMap.adjoint A) ∘L π x ∘L B := rfl

theorem compress_cp (hS : StinespringThm) (π : M →⋆ₐ[ℂ] (F →L[ℂ] F)) (A : E →L[ℂ] F) :
    IsCP (compress π A A) :=
  (hS M E (compress π A A)).2 ⟨F, inferInstance, inferInstance, inferInstance, π, A, fun _ => rfl⟩

theorem norm_compress_one_le (π : M →⋆ₐ[ℂ] (F →L[ℂ] F)) (A : E →L[ℂ] F) :
    ‖compress π A A 1‖ ≤ ‖A‖ ^ 2 := by
  rw [compress_apply, map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  calc ‖(ContinuousLinearMap.adjoint A) ∘L A‖
      ≤ ‖ContinuousLinearMap.adjoint A‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖A‖ ^ 2 := by rw [LinearIsometryEquiv.norm_map, sq]

theorem compress_cb_self (hF : CPMapFacts) (hS : StinespringThm) (π : M →⋆ₐ[ℂ] (F →L[ℂ] F))
    (A : E →L[ℂ] F) : CBBound (compress π A A) (‖A‖ ^ 2) :=
  (cb_of_cp hF (compress_cp hS π A)).mono (norm_compress_one_le π A)

theorem compress_expand (π : M →⋆ₐ[ℂ] (F →L[ℂ] F)) (A B : E →L[ℂ] F) (c : ℂ) :
    compress π (B + c • A) (B + c • A) = compress π B B + c • compress π B A
      + (starRingEnd ℂ c) • compress π A B + (starRingEnd ℂ c * c) • compress π A A := by
  ext x : 1
  simp only [LinearMap.add_apply, LinearMap.smul_apply, compress_apply, map_add, map_smulₛₗ,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul]
  module

/-- Polarization: `A† T B = ¼ [ (B+A)†T(B+A) + i (B+iA)†T(B+iA) - (B-A)†T(B-A) - i (B-iA)†T(B-iA) ]`. -/
theorem compress_polar (π : M →⋆ₐ[ℂ] (F →L[ℂ] F)) (A B : E →L[ℂ] F) :
    compress π A B = (1 / 4 : ℂ) • (compress π (B + (1 : ℂ) • A) (B + (1 : ℂ) • A)
      + Complex.I • compress π (B + Complex.I • A) (B + Complex.I • A)
      - compress π (B + (-1 : ℂ) • A) (B + (-1 : ℂ) • A)
      - Complex.I • compress π (B + (-Complex.I) • A) (B + (-Complex.I) • A)) := by
  rw [compress_expand, compress_expand, compress_expand, compress_expand]
  match_scalars
  all_goals
    (try simp only [map_one, map_neg, Complex.conj_I, neg_mul, mul_neg, neg_neg,
      Complex.I_mul_I, mul_one, one_mul]
     ring)

/-- `x ↦ A† π(x) B` is completely bounded with constant `(‖A‖ + ‖B‖)²`. -/
theorem compress_cb (hF : CPMapFacts) (hS : StinespringThm) (π : M →⋆ₐ[ℂ] (F →L[ℂ] F))
    (A B : E →L[ℂ] F) : CBBound (compress π A B) ((‖A‖ + ‖B‖) ^ 2) := by
  rw [compress_polar]
  have hn : ∀ c : ℂ, ‖c‖ = 1 → ‖B + c • A‖ ≤ ‖A‖ + ‖B‖ := fun c hc => by
    calc ‖B + c • A‖ ≤ ‖B‖ + ‖c • A‖ := norm_add_le _ _
      _ = ‖A‖ + ‖B‖ := by rw [norm_smul, hc, one_mul, add_comm]
  have h1 := compress_cb_self hF hS π (B + (1 : ℂ) • A)
  have h2 := (compress_cb_self hF hS π (B + Complex.I • A)).smul Complex.I
  have h3 := compress_cb_self hF hS π (B + (-1 : ℂ) • A)
  have h4 := (compress_cb_self hF hS π (B + (-Complex.I) • A)).smul Complex.I
  have hsum := (((h1.add h2).sub h3).sub h4).smul (1 / 4 : ℂ)
  refine hsum.mono ?_
  have e1 := hn 1 (by simp)
  have e2 := hn Complex.I (by simp)
  have e3 := hn (-1) (by simp)
  have e4 := hn (-Complex.I) (by simp)
  rw [Complex.norm_I, show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
  have hAB : 0 ≤ ‖A‖ + ‖B‖ := by positivity
  have s1 : ‖B + (1 : ℂ) • A‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 := by gcongr
  have s2 : ‖B + Complex.I • A‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 := by gcongr
  have s3 : ‖B + (-1 : ℂ) • A‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 := by gcongr
  have s4 : ‖B + (-Complex.I) • A‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 := by gcongr
  nlinarith

end Compress

section Block

variable {m : ℕ} {d : Fin m → ℕ}

/-- `Mₙ(⊕ⱼ M_{dⱼ}(ℂ)) ≃⋆ₐ ⊕ⱼ Mₙ(M_{dⱼ}(ℂ))`. -/
def blockMatEquiv (n : ℕ) : Mat n (BlockAlg d) ≃⋆ₐ[ℂ] ((j : Fin m) → Mat n (Mat (d j) ℂ)) where
  toFun X j := CStarMatrix.ofMatrix fun k l => X k l j
  invFun Y := CStarMatrix.ofMatrix fun k l j => Y j k l
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' X Y := by
    funext j
    refine CStarMatrix.ext fun k l => ?_
    change ((X * Y) k l) j = ((CStarMatrix.ofMatrix fun k l => X k l j) *
      (CStarMatrix.ofMatrix fun k l => Y k l j)) k l
    rw [CStarMatrix.mul_apply, CStarMatrix.mul_apply, Finset.sum_apply]
    rfl
  map_add' X Y := by funext j; exact CStarMatrix.ext fun k l => rfl
  map_star' X := by
    funext j
    refine CStarMatrix.ext fun k l => ?_
    change (star X k l) j = star (CStarMatrix.ofMatrix (fun k l => X k l j)) k l
    rw [CStarMatrix.star_apply, CStarMatrix.star_apply]
    rfl
  map_smul' c X := by funext j; exact CStarMatrix.ext fun k l => rfl

theorem blockMatEquiv_apply (n : ℕ) (X : Mat n (BlockAlg d)) (j : Fin m) (k l : Fin n) :
    blockMatEquiv n X j k l = X k l j := rfl

theorem blockMatEquiv_amp {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    (n : ℕ) (φ : M →ₗ[ℂ] BlockAlg d) (X : Mat n M) (j : Fin m) :
    blockMatEquiv n (X.map φ) j = X.map (LinearMap.proj j ∘ₗ φ) := rfl

theorem norm_le_of_blocks (n : ℕ) (X : Mat n (BlockAlg d)) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, ‖blockMatEquiv n X j‖ ≤ c) : ‖X‖ ≤ c := by
  rw [← StarAlgEquiv.norm_map (blockMatEquiv n) X]
  exact (pi_norm_le_iff_of_nonneg hc).2 h

theorem norm_block_le (n : ℕ) (X : Mat n (BlockAlg d)) (j : Fin m) :
    ‖blockMatEquiv n X j‖ ≤ ‖X‖ := by
  rw [← StarAlgEquiv.norm_map (blockMatEquiv n) X]
  exact norm_le_pi_norm _ j

theorem nonneg_of_blocks (n : ℕ) (X : Mat n (BlockAlg d))
    (h : ∀ j, 0 ≤ blockMatEquiv n X j) : 0 ≤ X := by
  have h' : blockMatEquiv n 0 ≤ blockMatEquiv n X := by
    rw [map_zero]; exact fun j => h j
  exact (NonUnitalStarAlgHom.map_le_map_iff (blockMatEquiv n) (blockMatEquiv n).injective).1 h'

theorem IsCP.of_blocks {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    (φ : M →ₗ[ℂ] BlockAlg d) (h : ∀ j, IsCP (LinearMap.proj j ∘ₗ φ)) : IsCP φ :=
  fun n X hX => nonneg_of_blocks n _ fun j => by rw [blockMatEquiv_amp]; exact h j n X hX

theorem CBBound.of_blocks {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    (φ : M →ₗ[ℂ] BlockAlg d) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, CBBound (LinearMap.proj j ∘ₗ φ) c) : CBBound φ c :=
  fun n X => norm_le_of_blocks n _ (by positivity) fun j => by
    rw [blockMatEquiv_amp]; exact h j n X

end Block

section MatCLM

/-- `M_d(ℂ) ≃⋆ₐ B(ℂ^d)`. -/
def matCLM (d : ℕ) : Mat d ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :=
  (CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ)).symm.trans Matrix.toEuclideanCLM

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- Transport a map into `B(ℂ^d)` to a map into `M_d(ℂ)`. -/
def toMat {d : ℕ} (φ : M →ₗ[ℂ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))) :
    M →ₗ[ℂ] Mat d ℂ :=
  (matCLM d).symm.toStarAlgHom.toAlgHom.toLinearMap ∘ₗ φ

theorem toMat_apply {d : ℕ}
    (φ : M →ₗ[ℂ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))) (x : M) :
    toMat φ x = (matCLM d).symm (φ x) := rfl

theorem toMat_cp {d : ℕ} {φ : M →ₗ[ℂ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))}
    (h : IsCP φ) : IsCP (toMat φ) :=
  (IsCP.ofStarAlgHom (matCLM d).symm.toStarAlgHom).comp h

theorem toMat_cb {d : ℕ} {φ : M →ₗ[ℂ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))}
    {c : ℝ} (h : CBBound φ c) : CBBound (toMat φ) c := fun n X => by
  have hinj : Function.Injective (matHom n (matCLM d).symm.toStarAlgHom) := by
    intro Y Z hYZ
    refine CStarMatrix.ext fun k l => ?_
    have := congrArg (fun W : Mat n (Mat d ℂ) => W k l) hYZ
    exact (matCLM d).symm.injective this
  have := NonUnitalStarAlgHom.norm_map _ hinj (X.map φ)
  calc ‖X.map (toMat φ)‖ = ‖X.map φ‖ := this
    _ ≤ c * ‖X‖ := h n X

end MatCLM

end Cert.KitaevChannels
