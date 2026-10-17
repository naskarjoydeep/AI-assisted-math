import Certs.KitaevSectors.Statement
import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Proof of Theorem B (sector theorem), conditional on Kitaev's Theorem 2.3

Informal proof (note, Proposition 3.1 and Theorem B):

* S1. Apply Kitaev's Theorem 2.3 to each sector `A i` (finite-dimensional, hence Banach):
  get C*-algebras `B i` and `(C ε)`-isomorphisms `v i : B i → A i`.
* S2. `ℓ^∞(B)` is a C*-algebra (nonzero because the index set is nonempty).
* S3. Because the constant `δ = C ε < 1` is uniform, `f ↦ (v i (f i))ᵢ` maps bounded families to
  bounded families, and so does `g ↦ (v i⁻¹ (g i))ᵢ` (norm `≤ ‖g‖/(1-δ)`): a linear bijection
  `ℓ^∞(B) ≃ ℓ^∞(A)`.
* S4. Every defining inequality of a δ-isomorphism holds coordinatewise with the same δ, hence
  for the suprema; the product, involution and unit of `T` are coordinatewise by hypothesis.
-/

open scoped ENNReal ComplexConjugate

noncomputable section

namespace Cert.KitaevSectors

variable {ι : Type*}

theorem norm_coord_le {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] (f : lp E ∞) (i : ι) :
    ‖f i‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero f i

/-- S2: the ℓ^∞-direct sum of C*-algebras is a C*-algebra (Mathlib supplies all the fields). -/
instance lpCStarAlgebra {B : ι → Type*} [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)] :
    CStarAlgebra (lp B ∞) where

/-- S2: it is nonzero when the index set is nonempty. -/
instance step2_nontrivial {B : ι → Type*} [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)]
    [Nonempty ι] : Nontrivial (lp B ∞) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrFun (congrArg (fun f : lp B ∞ => (f : ∀ i, B i)) h) i₀
  simp at this

section Iso

variable {A : ι → Type*} [∀ i, NormedAddCommGroup (A i)] [∀ i, NormedSpace ℂ (A i)]
  {B : ι → Type*} [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)]
  {ε δ : ℝ} {S : ∀ i, EpsCStar ε (A i)}

/-- S3: the coordinatewise map is a linear bijection `ℓ^∞(B) ≃ ℓ^∞(A)`; the uniform bound
`δ < 1` is what makes the inverse map bounded families to bounded families. -/
def step3_equiv (hδ0 : 0 ≤ δ) (hδ : δ < 1) (v : ∀ i, DeltaIso δ (ofCStarAlgebra (B i)) (S i)) :
    lp B ∞ ≃ₗ[ℂ] lp A ∞ where
  toFun f := ⟨fun i => (v i).toEquiv (f i), memℓp_infty ⟨(1 + δ) * ‖f‖, by
    rintro _ ⟨i, rfl⟩
    calc ‖(v i).toEquiv (f i)‖ ≤ (1 + δ) * ‖f i‖ := (v i).norm_map_le _
      _ ≤ (1 + δ) * ‖f‖ := mul_le_mul_of_nonneg_left (norm_coord_le f i) (by linarith)⟩⟩
  invFun g := ⟨fun i => (v i).toEquiv.symm (g i), memℓp_infty ⟨‖g‖ / (1 - δ), by
    rintro _ ⟨i, rfl⟩
    have h1 : 0 < 1 - δ := by linarith
    have hl := (v i).le_norm_map ((v i).toEquiv.symm (g i))
    rw [LinearEquiv.apply_symm_apply] at hl
    have := norm_coord_le g i
    simp only
    rw [le_div_iff₀ h1]
    linarith⟩⟩
  map_add' f g := lp.ext <| funext fun i => by
    change (v i).toEquiv (f i + g i) = (v i).toEquiv (f i) + (v i).toEquiv (g i)
    exact map_add _ _ _
  map_smul' c f := lp.ext <| funext fun i => by
    change (v i).toEquiv (c • f i) = c • (v i).toEquiv (f i)
    exact map_smul _ _ _
  left_inv f := lp.ext <| funext fun i => by
    change (v i).toEquiv.symm ((v i).toEquiv (f i)) = f i
    simp
  right_inv g := lp.ext <| funext fun i => by
    change (v i).toEquiv ((v i).toEquiv.symm (g i)) = g i
    simp

theorem step3_apply (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (v : ∀ i, DeltaIso δ (ofCStarAlgebra (B i)) (S i)) (f : lp B ∞) (i : ι) :
    step3_equiv hδ0 hδ v f i = (v i).toEquiv (f i) := rfl

/-- S4: the coordinatewise map is a δ-isomorphism onto any ε-C* structure `T` on `ℓ^∞(A)` whose
operations are coordinatewise. -/
def step4_deltaIso [Nonempty ι] (T : EpsCStar ε (lp A ∞))
    (hmul : ∀ f g i, T.mul f g i = (S i).mul (f i) (g i))
    (hstar : ∀ f i, T.star f i = (S i).star (f i))
    (hone : ∀ i, T.one i = (S i).one)
    (hδ0 : 0 ≤ δ) (hδ : δ < 1) (v : ∀ i, DeltaIso δ (ofCStarAlgebra (B i)) (S i)) :
    DeltaIso δ (ofCStarAlgebra (lp B ∞)) T where
  toEquiv := step3_equiv hδ0 hδ v
  map_star f := lp.ext <| funext fun i => by
    change (v i).toEquiv (star (f i)) = T.star (step3_equiv hδ0 hδ v f) i
    rw [hstar]
    exact (v i).map_star (f i)
  map_one_le := by
    refine lp.norm_le_of_forall_le hδ0 fun i => ?_
    change ‖(v i).toEquiv 1 - T.one i‖ ≤ δ
    rw [hone]
    exact (v i).map_one_le
  map_mul_le f g := by
    refine lp.norm_le_of_forall_le (by positivity) fun i => ?_
    change ‖(v i).toEquiv (f i * g i)
      - T.mul (step3_equiv hδ0 hδ v f) (step3_equiv hδ0 hδ v g) i‖ ≤ δ * ‖f‖ * ‖g‖
    rw [hmul]
    calc ‖(v i).toEquiv (f i * g i) - (S i).mul ((v i).toEquiv (f i)) ((v i).toEquiv (g i))‖
        ≤ δ * ‖f i‖ * ‖g i‖ := (v i).map_mul_le (f i) (g i)
      _ ≤ δ * ‖f‖ * ‖g‖ := by
          have := norm_coord_le f i
          have := norm_coord_le g i
          gcongr
  le_norm_map f := by
    have h1 : 0 < 1 - δ := by linarith
    have hf : ‖f‖ ≤ ‖step3_equiv hδ0 hδ v f‖ / (1 - δ) := by
      refine lp.norm_le_of_forall_le (div_nonneg (norm_nonneg _) h1.le) fun i => ?_
      rw [le_div_iff₀ h1]
      have h2 := (v i).le_norm_map (f i)
      have h3 := norm_coord_le (step3_equiv hδ0 hδ v f) i
      rw [step3_apply] at h3
      linarith
    rw [le_div_iff₀ h1] at hf
    change (1 - δ) * ‖f‖ ≤ ‖step3_equiv hδ0 hδ v f‖
    linarith
  norm_map_le f := by
    refine lp.norm_le_of_forall_le (by positivity) fun i => ?_
    calc ‖step3_equiv hδ0 hδ v f i‖ = ‖(v i).toEquiv (f i)‖ := rfl
      _ ≤ (1 + δ) * ‖f i‖ := (v i).norm_map_le _
      _ ≤ (1 + δ) * ‖f‖ := mul_le_mul_of_nonneg_left (norm_coord_le f i) (by linarith)

end Iso

/-- S1: Kitaev's Theorem 2.3 applies to every sector (finite-dimensional normed spaces over `ℂ`
are complete). -/
theorem step1 {C ε₀ : ℝ} (hK : KitaevFiniteDim C ε₀) {ε : ℝ} (hε : 0 ≤ ε) (hε₀ : ε < ε₀)
    (A : Type) [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
    (S : EpsCStar ε A) :
    ∃ (B : Type) (_ : CStarAlgebra B) (_ : Nontrivial B),
      Nonempty (DeltaIso (C * ε) (ofCStarAlgebra B) S) := by
  have : CompleteSpace A := FiniteDimensional.complete ℂ A
  exact hK A ε S hε hε₀

theorem main : Claim := by
  intro C ε₀ hK ε hε hε₀ hCε ι _ A _ _ _ S T hmul hstar hone
  choose B instB ntB v using fun i => step1 hK hε hε₀ (A i) (S i)
  let _ : ∀ i, CStarAlgebra (B i) := instB
  let _ : ∀ i, Nontrivial (B i) := ntB
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  -- `0 ≤ C ε` is forced: a δ-isomorphism has `0 ≤ ‖v(I) - I‖ ≤ δ`
  have hδ0 : 0 ≤ C * ε := (norm_nonneg _).trans (v i₀).some.map_one_le
  exact ⟨lp B ∞, inferInstance, step2_nontrivial,
    ⟨step4_deltaIso T hmul hstar hone hδ0 hCε (fun i => (v i).some)⟩⟩

end Cert.KitaevSectors
