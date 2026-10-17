import Certs.KitaevChannels.Statement
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Toolkit: amplifications, completely bounded and completely positive maps

Generic facts about `X.map φ` (the amplification `1_{Mₙ} ⊗ φ`), the predicates `CBBound`, `IsCP`,
entrywise star homomorphisms, and the diagonal embedding `M → Mₙ(M)`.
-/

open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

section Amp

variable {M₁ M₂ M₃ : Type*}
  [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
  [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂]
  [CStarAlgebra M₃] [PartialOrder M₃] [StarOrderedRing M₃]
  {n : ℕ}

@[simp] theorem amp_apply (X : Mat n M₁) (f : M₁ → M₂) (i j : Fin n) :
    X.map f i j = f (X i j) := rfl

theorem amp_comp (X : Mat n M₁) (φ : M₁ →ₗ[ℂ] M₂) (ψ : M₂ →ₗ[ℂ] M₃) :
    X.map (ψ ∘ₗ φ) = (X.map φ).map ψ := rfl

theorem amp_add_fun (X : Mat n M₁) (φ ψ : M₁ →ₗ[ℂ] M₂) :
    X.map (φ + ψ) = X.map φ + X.map ψ := by
  ext i j; rfl

theorem amp_sub_fun (X : Mat n M₁) (φ ψ : M₁ →ₗ[ℂ] M₂) :
    X.map (φ - ψ) = X.map φ - X.map ψ := by
  ext i j; rfl

theorem amp_smul_fun (X : Mat n M₁) (c : ℂ) (φ : M₁ →ₗ[ℂ] M₂) :
    X.map (c • φ) = c • X.map φ := by
  ext i j; rfl

theorem amp_zero_fun (X : Mat n M₁) : X.map (0 : M₁ →ₗ[ℂ] M₂) = 0 := by
  ext i j; rfl

theorem amp_id (X : Mat n M₁) : X.map (LinearMap.id : M₁ →ₗ[ℂ] M₁) = X := by
  ext i j; rfl

theorem amp_add (X Y : Mat n M₁) (φ : M₁ →ₗ[ℂ] M₂) : (X + Y).map φ = X.map φ + Y.map φ := by
  ext i j; exact map_add φ _ _

theorem amp_sub (X Y : Mat n M₁) (φ : M₁ →ₗ[ℂ] M₂) : (X - Y).map φ = X.map φ - Y.map φ := by
  ext i j; exact map_sub φ _ _

theorem amp_smul (X : Mat n M₁) (c : ℂ) (φ : M₁ →ₗ[ℂ] M₂) : (c • X).map φ = c • X.map φ := by
  ext i j; exact map_smul φ _ _

end Amp

section CB

variable {M₁ M₂ M₃ : Type*}
  [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
  [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂]
  [CStarAlgebra M₃] [PartialOrder M₃] [StarOrderedRing M₃]

theorem CBBound.mono {φ : M₁ →ₗ[ℂ] M₂} {a b : ℝ} (h : CBBound φ a) (hab : a ≤ b) :
    CBBound φ b := fun n X => (h n X).trans (by gcongr)

theorem CBBound.comp {φ : M₂ →ₗ[ℂ] M₃} {ψ : M₁ →ₗ[ℂ] M₂} {a b : ℝ} (ha : 0 ≤ a)
    (hφ : CBBound φ a) (hψ : CBBound ψ b) : CBBound (φ ∘ₗ ψ) (a * b) := fun n X => by
  rw [amp_comp]
  calc ‖(X.map ψ).map φ‖ ≤ a * ‖X.map ψ‖ := hφ n _
    _ ≤ a * (b * ‖X‖) := by gcongr; exact hψ n X
    _ = a * b * ‖X‖ := by ring

theorem CBBound.add {φ ψ : M₁ →ₗ[ℂ] M₂} {a b : ℝ} (hφ : CBBound φ a) (hψ : CBBound ψ b) :
    CBBound (φ + ψ) (a + b) := fun n X => by
  rw [amp_add_fun]
  calc ‖X.map φ + X.map ψ‖ ≤ ‖X.map φ‖ + ‖X.map ψ‖ := norm_add_le _ _
    _ ≤ a * ‖X‖ + b * ‖X‖ := add_le_add (hφ n X) (hψ n X)
    _ = (a + b) * ‖X‖ := by ring

theorem CBBound.sub {φ ψ : M₁ →ₗ[ℂ] M₂} {a b : ℝ} (hφ : CBBound φ a) (hψ : CBBound ψ b) :
    CBBound (φ - ψ) (a + b) := fun n X => by
  rw [amp_sub_fun]
  calc ‖X.map φ - X.map ψ‖ ≤ ‖X.map φ‖ + ‖X.map ψ‖ := norm_sub_le _ _
    _ ≤ a * ‖X‖ + b * ‖X‖ := add_le_add (hφ n X) (hψ n X)
    _ = (a + b) * ‖X‖ := by ring

theorem CBBound.smul {φ : M₁ →ₗ[ℂ] M₂} {a : ℝ} (c : ℂ) (hφ : CBBound φ a) :
    CBBound (c • φ) (‖c‖ * a) := fun n X => by
  rw [amp_smul_fun, norm_smul]
  calc ‖c‖ * ‖X.map φ‖ ≤ ‖c‖ * (a * ‖X‖) := by gcongr; exact hφ n X
    _ = ‖c‖ * a * ‖X‖ := by ring

theorem CBBound.zero : CBBound (0 : M₁ →ₗ[ℂ] M₂) 0 := fun n X => by
  rw [amp_zero_fun]; simp

theorem CBBound.sum {ι : Type*} (s : Finset ι) (φ : ι → M₁ →ₗ[ℂ] M₂) (a : ι → ℝ)
    (h : ∀ i ∈ s, CBBound (φ i) (a i)) : CBBound (∑ i ∈ s, φ i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CBBound.zero : CBBound (0 : M₁ →ₗ[ℂ] M₂) 0)
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact (h b (Finset.mem_insert_self b s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CBBound.id : CBBound (LinearMap.id : M₁ →ₗ[ℂ] M₁) 1 := fun n X => by
  rw [amp_id, one_mul]

end CB

section CP

variable {M₁ M₂ M₃ : Type*}
  [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
  [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂]
  [CStarAlgebra M₃] [PartialOrder M₃] [StarOrderedRing M₃]

theorem IsCP.comp {φ : M₂ →ₗ[ℂ] M₃} {ψ : M₁ →ₗ[ℂ] M₂} (hφ : IsCP φ) (hψ : IsCP ψ) :
    IsCP (φ ∘ₗ ψ) := fun n X hX => by
  rw [amp_comp]; exact hφ n _ (hψ n X hX)

theorem IsCP.add {φ ψ : M₁ →ₗ[ℂ] M₂} (hφ : IsCP φ) (hψ : IsCP ψ) : IsCP (φ + ψ) :=
  fun n X hX => by rw [amp_add_fun]; exact add_nonneg (hφ n X hX) (hψ n X hX)

theorem IsCP.zero : IsCP (0 : M₁ →ₗ[ℂ] M₂) := fun n X _ => by rw [amp_zero_fun]

theorem IsCP.sum {ι : Type*} (s : Finset ι) (φ : ι → M₁ →ₗ[ℂ] M₂) (h : ∀ i ∈ s, IsCP (φ i)) :
    IsCP (∑ i ∈ s, φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsCP.zero : IsCP (0 : M₁ →ₗ[ℂ] M₂))
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact (h b (Finset.mem_insert_self b s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The constant diagonal matrix `diag(x, …, x)`. -/
def diagM {M : Type*} [Zero M] (n : ℕ) (x : M) : Mat n M :=
  CStarMatrix.ofMatrix (Matrix.diagonal fun _ => x)

theorem diagM_apply {M : Type*} [Zero M] (n : ℕ) (x : M) (i j : Fin n) :
    diagM n x i j = if i = j then x else 0 := by
  simp [diagM, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply]

theorem diagM_mul_left {n : ℕ} (x : M₂) (X : Mat n M₂) (i j : Fin n) :
    (diagM n x * X) i j = x * X i j := by
  rw [CStarMatrix.mul_apply]
  simp [diagM_apply]

theorem mul_diagM_right {n : ℕ} (x : M₂) (X : Mat n M₂) (i j : Fin n) :
    (X * diagM n x) i j = X i j * x := by
  rw [CStarMatrix.mul_apply]
  simp [diagM_apply]

theorem star_diagM {n : ℕ} (x : M₂) : star (diagM n x) = diagM n (star x) := by
  ext i j
  rw [CStarMatrix.star_apply, diagM_apply, diagM_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The two-sided multiplication `x ↦ a * x * b` as a linear map. -/
def lrMul (a b : M₂) : M₂ →ₗ[ℂ] M₂ where
  toFun x := a * x * b
  map_add' x y := by rw [mul_add, add_mul]
  map_smul' c x := by simp [smul_mul_assoc]

theorem amp_lrMul {n : ℕ} (a b : M₂) (X : Mat n M₂) :
    X.map (lrMul a b) = diagM n a * X * diagM n b := by
  ext i j
  rw [mul_diagM_right, diagM_mul_left]
  rfl

/-- Conjugations `x ↦ c† x c` are completely positive. -/
theorem IsCP.lrMul_star (c : M₂) : IsCP (lrMul (star c) c) := fun n X hX => by
  rw [amp_lrMul, ← star_diagM]
  exact star_left_conjugate_nonneg hX _

/-- Composing a CP map with a conjugation keeps it CP. -/
theorem IsCP.conj {φ : M₁ →ₗ[ℂ] M₂} (hφ : IsCP φ) (c : M₂) :
    IsCP (lrMul (star c) c ∘ₗ φ) := (IsCP.lrMul_star c).comp hφ

/-- Nonnegative real multiples of a CP map are CP (`r • x = (√r)† x (√r)`). -/
theorem IsCP.smul_nonneg {φ : M₁ →ₗ[ℂ] M₂} (hφ : IsCP φ) {r : ℝ} (hr : 0 ≤ r) :
    IsCP ((r : ℂ) • φ) := fun n X hX => by
  have key : ((r : ℂ) • φ) = lrMul (star ((Real.sqrt r : ℂ) • (1 : M₂)))
      ((Real.sqrt r : ℂ) • (1 : M₂)) ∘ₗ φ := by
    ext x
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, lrMul, LinearMap.coe_mk,
      AddHom.coe_mk, star_smul, star_one, RCLike.star_def, Complex.conj_ofReal, smul_mul_assoc,
      one_mul, mul_smul_comm, mul_one, smul_smul]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  rw [key]
  exact (hφ.conj _) n X hX

end CP

section Homs

variable {M₁ M₂ : Type*}
  [CStarAlgebra M₁] [PartialOrder M₁] [StarOrderedRing M₁]
  [CStarAlgebra M₂] [PartialOrder M₂] [StarOrderedRing M₂]

/-- Entrywise application of a star algebra homomorphism, as a star algebra homomorphism of
matrix algebras. -/
def matHom (n : ℕ) (π : M₁ →⋆ₐ[ℂ] M₂) : Mat n M₁ →⋆ₐ[ℂ] Mat n M₂ where
  toFun X := X.map π
  map_one' := by
    ext i j
    rw [amp_apply, CStarMatrix.one_apply, CStarMatrix.one_apply]
    split_ifs <;> simp
  map_mul' X Y := by
    ext i j
    simp only [amp_apply, CStarMatrix.mul_apply, map_sum, map_mul]
  map_zero' := by ext i j; simp
  map_add' X Y := by ext i j; simp
  commutes' r := by
    ext i j
    change π ((algebraMap ℂ (Mat n M₁) r) i j) = (algebraMap ℂ (Mat n M₂) r) i j
    rw [CStarMatrix.algebraMap_apply, CStarMatrix.algebraMap_apply]
    split_ifs
    · exact π.commutes r
    · exact map_zero π
  map_star' X := by
    ext i j
    simp only [amp_apply, CStarMatrix.star_apply, map_star]

theorem matHom_apply (n : ℕ) (π : M₁ →⋆ₐ[ℂ] M₂) (X : Mat n M₁) : matHom n π X = X.map π := rfl

/-- Star algebra homomorphisms are completely positive. -/
theorem IsCP.ofStarAlgHom (π : M₁ →⋆ₐ[ℂ] M₂) : IsCP (π.toAlgHom.toLinearMap) := fun n X hX => by
  have h := OrderHomClass.mono (matHom n π) hX
  rw [map_zero] at h
  exact h

/-- The diagonal embedding `M → Mₙ(M)`, `x ↦ diag(x,…,x)`. -/
def diagHom (n : ℕ) : M₂ →⋆ₐ[ℂ] Mat n M₂ where
  toFun x := diagM n x
  map_one' := by ext i j; rw [diagM_apply, CStarMatrix.one_apply]
  map_mul' x y := by ext i j; rw [diagM_mul_left, diagM_apply, diagM_apply]; split_ifs <;> simp
  map_zero' := by ext i j; rw [diagM_apply]; split_ifs <;> rfl
  map_add' x y := by
    ext i j
    change diagM n (x + y) i j = diagM n x i j + diagM n y i j
    simp only [diagM_apply]; split_ifs <;> simp
  commutes' r := by
    ext i j
    change diagM n (algebraMap ℂ M₂ r) i j = (algebraMap ℂ (Mat n M₂) r) i j
    rw [diagM_apply, CStarMatrix.algebraMap_apply]
  map_star' x := (star_diagM x).symm

theorem norm_diagM_le (n : ℕ) (x : M₂) : ‖diagM n x‖ ≤ ‖x‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : diagM 0 x = 0 := by ext i; exact i.elim0
    rw [this, norm_zero]; exact norm_nonneg _
  · have hinj : Function.Injective (diagHom (M₂ := M₂) n) := fun x y h => by
      have := congrArg (fun X : Mat n M₂ => X ⟨0, hn⟩ ⟨0, hn⟩) h
      simpa [diagHom, diagM_apply] using this
    exact (NonUnitalStarAlgHom.norm_map (diagHom (M₂ := M₂) n) hinj x).le

theorem amp_diagM {M₃ : Type*} [CStarAlgebra M₃] [PartialOrder M₃] [StarOrderedRing M₃]
    (n : ℕ) (φ : M₂ →ₗ[ℂ] M₃) (x : M₂) : (diagM n x).map φ = diagM n (φ x) := by
  ext i j
  rw [amp_apply, diagM_apply, diagM_apply]
  split_ifs <;> simp

theorem norm_diagM_one (x : M₂) : ‖diagM 1 x‖ = ‖x‖ := by
  have hinj : Function.Injective (diagHom (M₂ := M₂) 1) := fun x y h => by
    have := congrArg (fun X : Mat 1 M₂ => X 0 0) h
    simpa [diagHom, diagM_apply] using this
  exact NonUnitalStarAlgHom.norm_map (diagHom (M₂ := M₂) 1) hinj x

/-- A completely bounded map is bounded (level `n = 1`). -/
theorem CBBound.apply_le {M₃ : Type*} [CStarAlgebra M₃] [PartialOrder M₃] [StarOrderedRing M₃]
    {φ : M₂ →ₗ[ℂ] M₃} {c : ℝ} (h : CBBound φ c) (x : M₂) : ‖φ x‖ ≤ c * ‖x‖ := by
  have := h 1 (diagM 1 x)
  rwa [amp_diagM, norm_diagM_one, norm_diagM_one] at this

end Homs

end Cert.KitaevChannels
