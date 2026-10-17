import Certs.KitaevChannels.Normalize
import Mathlib.Data.Matrix.Basis
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A norm-one diagonal of `⊕ⱼ M_{dⱼ}(ℂ)` as an average over unitaries

Kitaev (§8, after (8.6), and §12.2) combines per-block unitary 1-designs into a product design on
`⊕ⱼ M_{dⱼ}`. That product is **not** a diagonal when there are ≥ 2 blocks (for `ℂ ⊕ ℂ` with the
trivial designs it is `I ⊗ I`), because the cross-block terms carry the first moments
`∑ pₛ Uₛ ≠ 0`. We repair it by attaching an independent uniform sign `±1` to each block, which
kills every cross-block term; the per-block twirl identity then gives the diagonal identity
`∑ₛ pₛ β(a x uₛ†, uₛ) = ∑ₛ pₛ β(a uₛ†, uₛ x)` for every bilinear `β`.
-/

open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

/-- A unitary 1-design on `M_d(ℂ)`. -/
structure Design (d : ℕ) where
  S : Type
  [fin : Fintype S]
  p : S → ℝ
  U : S → Mat d ℂ
  p_nonneg : ∀ s, 0 ≤ p s
  p_sum : ∑ s, p s = 1
  unit : ∀ s, star (U s) * U s = 1 ∧ U s * star (U s) = 1
  twirl : ∀ a b c e : Fin d, ∑ s, (p s : ℂ) * star (U s b a) * U s c e =
    if a = e ∧ b = c then 1 / (d : ℂ) else 0

attribute [instance] Design.fin

/-- The design supplied by the assumption `UnitaryDesign`. -/
def Design.ofHyp (hD : UnitaryDesign) (d : ℕ) : Design d := by
  choose S inst p U hp hs hu ht using hD d
  exact ⟨S, p, U, hp, hs, hu, ht⟩

section Coord

variable {d : ℕ}

/-- The matrix unit `E_{ab}`. -/
def E (a b : Fin d) : Mat d ℂ := CStarMatrix.ofMatrix (Matrix.single a b 1)

theorem cm_eq_sum (M : Mat d ℂ) : M = ∑ a, ∑ b, M a b • E a b := by
  refine CStarMatrix.ext fun i j => ?_
  change M i j = (∑ a, ∑ b, (M a b • (Matrix.single a b (1 : ℂ) : Matrix (Fin d) (Fin d) ℂ))) i j
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq']

theorem bil_expand {V : Type*} [AddCommGroup V] [Module ℂ V]
    (β : Mat d ℂ →ₗ[ℂ] Mat d ℂ →ₗ[ℂ] V) (P Q : Mat d ℂ) :
    β P Q = ∑ c, ∑ e, ∑ a, ∑ b, (Q c e * P a b) • β (E a b) (E c e) := by
  conv_lhs => rw [cm_eq_sum P, cm_eq_sum Q]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]

/-- Exchanging the design sum with the coordinate expansion. -/
theorem sum_bil_expand {V : Type*} [AddCommGroup V] [Module ℂ V] {T : Type} [Fintype T]
    (β : Mat d ℂ →ₗ[ℂ] Mat d ℂ →ₗ[ℂ] V) (w : T → ℂ) (P Q : T → Mat d ℂ) :
    ∑ t, w t • β (P t) (Q t) =
      ∑ c, ∑ e, ∑ a, ∑ b, (∑ t, w t * (Q t c e * P t a b)) • β (E a b) (E c e) := by
  have h1 : ∀ t, w t • β (P t) (Q t) =
      ∑ c, ∑ e, ∑ a, ∑ b, (w t * (Q t c e * P t a b)) • β (E a b) (E c e) := fun t => by
    rw [bil_expand β (P t) (Q t)]
    simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_congr rfl fun t _ => h1 t]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_smul]

theorem coeff_left (D : Design d) (x : Mat d ℂ) (a b c e : Fin d) :
    ∑ t, (D.p t : ℂ) * (D.U t c e * (x * star (D.U t)) a b) =
      if b = c then x a e / d else 0 := by
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ g, ∑ t, (D.p t : ℂ) * (D.U t c e * (x a g * star (D.U t b g))) =
      x a g * ∑ t, (D.p t : ℂ) * star (D.U t b g) * D.U t c e := fun g => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring
  simp only [this, D.twirl]
  by_cases hbc : b = c
  · simp [hbc, div_eq_mul_inv]
  · simp [hbc]

theorem coeff_right (D : Design d) (x : Mat d ℂ) (a b c e : Fin d) :
    ∑ t, (D.p t : ℂ) * ((D.U t * x) c e * star (D.U t) a b) =
      if b = c then x a e / d else 0 := by
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ g, ∑ t, (D.p t : ℂ) * (D.U t c g * x g e * star (D.U t b a)) =
      (∑ t, (D.p t : ℂ) * star (D.U t b a) * D.U t c g) * x g e := fun g => by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun t _ => by ring
  simp only [this, D.twirl]
  by_cases hbc : b = c
  · simp [hbc, div_eq_mul_inv, mul_comm]
  · simp [hbc]

/-- The per-block diagonal identity. -/
theorem Design.diag (D : Design d) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (β : Mat d ℂ →ₗ[ℂ] Mat d ℂ →ₗ[ℂ] V) (x : Mat d ℂ) :
    ∑ t, (D.p t : ℂ) • β (x * star (D.U t)) (D.U t) =
      ∑ t, (D.p t : ℂ) • β (star (D.U t)) (D.U t * x) := by
  rw [sum_bil_expand β (fun t => (D.p t : ℂ)) (fun t => x * star (D.U t)) D.U,
    sum_bil_expand β (fun t => (D.p t : ℂ)) (fun t => star (D.U t)) (fun t => D.U t * x)]
  simp only [coeff_left, coeff_right]

end Coord

section Block

variable {m : ℕ} {d : Fin m → ℕ} (D : (j : Fin m) → Design (d j))

/-- Signed design index for block `j`. -/
abbrev SIdx (j : Fin m) : Type := (D j).S × Bool

/-- `±1`. -/
def sgn (b : Bool) : ℂ := if b then 1 else -1

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

theorem star_sgn (b : Bool) : star (sgn b) = sgn b := by cases b <;> simp [sgn]

/-- Global design index. -/
abbrev GIdx : Type := (j : Fin m) → SIdx D j

/-- Weight of a signed index. -/
def wt (j : Fin m) (q : SIdx D j) : ℝ := (D j).p q.1 / 2

/-- Product weights. -/
def pg (s : GIdx D) : ℝ := ∏ j, wt D j (s j)

/-- The unitaries `u_s = ⊕ⱼ ±U_{j, s_j}`. -/
def ug (s : GIdx D) : BlockAlg d := fun j => sgn (s j).2 • (D j).U (s j).1

theorem pg_nonneg (s : GIdx D) : 0 ≤ pg D s :=
  Finset.prod_nonneg fun j _ => div_nonneg ((D j).p_nonneg _) (by norm_num)

theorem wt_sum (j : Fin m) : ∑ q : SIdx D j, wt D j q = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [wt, Fintype.sum_bool]
  rw [← (D j).p_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem pg_sum : ∑ s, pg D s = 1 := by
  unfold pg
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  exact Finset.prod_eq_one fun j _ => wt_sum D j

theorem ug_unitary (s : GIdx D) : star (ug D s) * ug D s = 1 ∧ ug D s * star (ug D s) = 1 := by
  constructor <;> funext j <;>
    simp only [ug, Pi.mul_apply, Pi.star_apply, Pi.one_apply, star_smul, star_sgn,
      smul_mul_smul_comm, sgn_mul_self, one_smul, ((D j).unit _).1, ((D j).unit _).2]

/-- Flip the sign bit of block `k`. -/
def flipAt (k : Fin m) : GIdx D ≃ GIdx D where
  toFun s := Function.update s k ((s k).1, !(s k).2)
  invFun s := Function.update s k ((s k).1, !(s k).2)
  left_inv s := by
    funext i
    by_cases h : i = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  right_inv s := by
    funext i
    by_cases h : i = k
    · subst h; simp
    · simp [Function.update_of_ne h]

theorem pg_flipAt (k : Fin m) (s : GIdx D) : pg D (flipAt D k s) = pg D s := by
  unfold pg
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : i = k
  · subst h; simp [flipAt, wt]
  · simp [flipAt, Function.update_of_ne h]

/-- Cross-block terms vanish: averaging the sign of block `k` kills anything that does not
otherwise depend on that sign. -/
theorem cross_vanish {V : Type*} [AddCommGroup V] [Module ℂ V] {j k : Fin m} (hjk : j ≠ k)
    (G : SIdx D j → (D k).S → V) :
    ∑ s, (pg D s : ℂ) • (sgn (s k).2 • G (s j) (s k).1) = 0 := by
  set T := ∑ s, (pg D s : ℂ) • (sgn (s k).2 • G (s j) (s k).1) with hT
  have hflip : T = -T := by
    conv_lhs => rw [hT, ← Equiv.sum_comp (flipAt D k)]
    rw [hT, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hj : (flipAt D k s) j = s j := by simp [flipAt, Function.update_of_ne hjk]
    have hk : (flipAt D k s) k = ((s k).1, !(s k).2) := by simp [flipAt]
    rw [pg_flipAt, hj, hk]
    cases (s k).2 <;> simp [sgn]
  have : (2 : ℂ) • T = 0 := by rw [two_smul]; nth_rewrite 2 [hflip]; exact add_neg_cancel T
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

/-- Marginal of block `j`. -/
theorem marginal {V : Type*} [AddCommGroup V] [Module ℂ V] (j : Fin m) (F : (D j).S → V) :
    ∑ s, (pg D s : ℂ) • F (s j).1 = ∑ t, ((D j).p t : ℂ) • F t := by
  classical
  have hind : ∀ s : GIdx D, F (s j).1 = ∑ q : SIdx D j, (if s j = q then (1 : ℂ) else 0) • F q.1 :=
    fun s => by simp [Finset.sum_ite_eq]
  have hw : ∀ q : SIdx D j, ∑ s : GIdx D, (pg D s : ℂ) * (if s j = q then 1 else 0) = wt D j q := by
    intro q
    let g : (i : Fin m) → SIdx D i → ℝ :=
      Function.update (fun i r => wt D i r) j (fun r => wt D j r * (if r = q then 1 else 0))
    have hprod : ∀ s : GIdx D, (pg D s : ℂ) * (if s j = q then 1 else 0) = ((∏ i, g i (s i) : ℝ) : ℂ) := by
      intro s
      unfold pg
      rw [← Finset.mul_prod_erase Finset.univ (fun i => g i (s i)) (Finset.mem_univ j),
        ← Finset.mul_prod_erase Finset.univ (fun i => wt D i (s i)) (Finset.mem_univ j)]
      have he : ∏ i ∈ Finset.univ.erase j, g i (s i) = ∏ i ∈ Finset.univ.erase j, wt D i (s i) :=
        Finset.prod_congr rfl fun i hi => by simp [g, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [he]
      simp only [g, Function.update_self]
      split_ifs <;> push_cast <;> ring
    simp only [hprod]
    rw [← Complex.ofReal_sum, ← Fintype.piFinset_univ, ← Finset.prod_univ_sum,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    have he : ∏ i ∈ Finset.univ.erase j, ∑ r, g i r = 1 :=
      Finset.prod_eq_one fun i hi => by
        simp only [g, Function.update_of_ne (Finset.ne_of_mem_erase hi)]; exact wt_sum D i
    rw [he, mul_one]
    simp [g, Finset.sum_ite_eq']
  calc ∑ s, (pg D s : ℂ) • F (s j).1
      = ∑ s, ∑ q : SIdx D j, ((pg D s : ℂ) * (if s j = q then 1 else 0)) • F q.1 := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hind s, Finset.smul_sum]
        simp only [smul_smul]
    _ = ∑ q : SIdx D j, (wt D j q : ℂ) • F q.1 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← Finset.sum_smul, hw q]
    _ = ∑ t, ((D j).p t : ℂ) • F t := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [wt, Fintype.sum_bool, ← add_smul]
        congr 1; push_cast; ring

/-- Block embedding `M_{dⱼ} → ⊕ₖ M_{dₖ}`. -/
abbrev ιb (j : Fin m) : Mat (d j) ℂ →ₗ[ℂ] BlockAlg d := LinearMap.single ℂ (fun j => Mat (d j) ℂ) j

theorem blk_sum (z : BlockAlg d) : z = ∑ j, ιb j (z j) := by
  simp only [ιb, LinearMap.coe_single]
  exact (Finset.univ_sum_single z).symm

theorem avg_expand {V : Type*} [AddCommGroup V] [Module ℂ V]
    (β : BlockAlg d →ₗ[ℂ] BlockAlg d →ₗ[ℂ] V) (F G : ∀ j, (D j).S → Mat (d j) ℂ) :
    ∑ s, (pg D s : ℂ) • β (fun j => sgn (s j).2 • F j (s j).1) (fun j => sgn (s j).2 • G j (s j).1)
      = ∑ j, ∑ t, ((D j).p t : ℂ) • β (ιb j (F j t)) (ιb j (G j t)) := by
  have hexp : ∀ s : GIdx D, β (fun j => sgn (s j).2 • F j (s j).1) (fun j => sgn (s j).2 • G j (s j).1)
      = ∑ j, ∑ k, (sgn (s k).2 • (sgn (s j).2 • β (ιb j (F j (s j).1)) (ιb k (G k (s k).1)))) := by
    intro s
    conv_lhs => rw [blk_sum (fun j => sgn (s j).2 • F j (s j).1),
      blk_sum (fun j => sgn (s j).2 • G j (s j).1)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
  simp only [hexp, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.sum_eq_single j]
  · have : ∀ s : GIdx D, (pg D s : ℂ) • (sgn (s j).2 • (sgn (s j).2 •
        β (ιb j (F j (s j).1)) (ιb j (G j (s j).1)))) =
        (pg D s : ℂ) • β (ιb j (F j (s j).1)) (ιb j (G j (s j).1)) := fun s => by
      rw [smul_smul, smul_smul, mul_assoc, sgn_mul_self, mul_one]
    simp only [this]
    exact marginal D j (fun t => β (ιb j (F j t)) (ιb j (G j t)))
  · intro k _ hkj
    exact cross_vanish D (Ne.symm hkj)
      (fun q t => sgn q.2 • β (ιb j (F j q.1)) (ιb k (G k t)))
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The diagonal identity** for the signed product design on `⊕ⱼ M_{dⱼ}(ℂ)`. -/
theorem diag_block {V : Type*} [AddCommGroup V] [Module ℂ V]
    (β : BlockAlg d →ₗ[ℂ] BlockAlg d →ₗ[ℂ] V) (a x : BlockAlg d) :
    ∑ s, (pg D s : ℂ) • β (a * x * star (ug D s)) (ug D s) =
      ∑ s, (pg D s : ℂ) • β (a * star (ug D s)) (ug D s * x) := by
  have e1 : ∀ s, a * x * star (ug D s) =
      fun j => sgn (s j).2 • (a j * x j * star ((D j).U (s j).1)) := fun s => by
    funext j; simp only [ug, Pi.mul_apply, Pi.star_apply, star_smul, star_sgn, mul_smul_comm]
  have e2 : ∀ s, a * star (ug D s) = fun j => sgn (s j).2 • (a j * star ((D j).U (s j).1)) :=
    fun s => by funext j; simp only [ug, Pi.mul_apply, Pi.star_apply, star_smul, star_sgn, mul_smul_comm]
  have e3 : ∀ s, ug D s * x = fun j => sgn (s j).2 • ((D j).U (s j).1 * x j) := fun s => by
    funext j; simp only [ug, Pi.mul_apply, smul_mul_assoc]
  have e4 : ∀ s, ug D s = fun j => sgn (s j).2 • (D j).U (s j).1 := fun s => rfl
  simp only [e1, e2, e3]
  conv_lhs => arg 2; ext s; rw [e4 s]
  rw [avg_expand D β (fun j t => a j * x j * star ((D j).U t)) (fun j t => (D j).U t),
    avg_expand D β (fun j t => a j * star ((D j).U t)) (fun j t => (D j).U t * x j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  let βj : Mat (d j) ℂ →ₗ[ℂ] Mat (d j) ℂ →ₗ[ℂ] V :=
    (β.comp ((ιb j).comp (LinearMap.mulLeft ℂ (a j)))).compl₂ (ιb j)
  have := (D j).diag βj (x j)
  simpa [βj, mul_assoc] using this

end Block

end Cert.KitaevChannels
