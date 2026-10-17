import Certs.KitaevChannels.DeltaUCP

/-!
# Properties (12.34)–(12.36) of `Δ` at every matrix level

From `‖Δ - Δ̃‖_cb ≤ e`, `Φ̃ Δ̃ = Δ̃`, (12.27) and, for (12.36), Kitaev's equation (12.6).
-/

open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

/-- The standing data and hypotheses of §12.2. -/
structure Ctx (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)
  η : ℝ
  δ : ℝ
  e : ℝ
  ε₁ : ℝ
  m : ℕ
  d : Fin m → ℕ
  v : BlockAlg d →ₗ[ℂ] (H →L[ℂ] H)
  Δ : BlockAlg d →ₗ[ℂ] (H →L[ℂ] H)
  hF : CPMapFacts
  hA : ExtEpsCStarSub ε₁ (LinearMap.range (tildePhi Φ).toLinearMap) (choiEffros Φ)
  hv : IsExtDeltaIsoOnto δ (LinearMap.range (tildePhi Φ).toLinearMap) (choiEffros Φ) v
  hΦ : IsUCP Φ.toLinearMap
  hcb : CBBound (Φ * Φ - Φ).toLinearMap η
  hη : 0 ≤ η
  hη8 : η ≤ 1 / 8
  hδ : 0 ≤ δ
  hΔ : IsUCP Δ
  hΔv : CBBound (Δ - v) e
  he : 0 ≤ e

namespace Ctx

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
  (C : Ctx H)

theorem tilde_comp_v : (tildePhi C.Φ).toLinearMap ∘ₗ C.v = C.v := by
  exact LinearMap.ext fun b => tilde_fix C.hA (v_mem C.hv b)

theorem phi_cb : CBBound C.Φ.toLinearMap 1 := cb_of_ucp C.hF C.hΦ

theorem delta_cb : CBBound C.Δ 1 := cb_of_ucp C.hF C.hΔ

theorem phi_tilde_close {n : ℕ} (X : Mat n (H →L[ℂ] H)) :
    ‖X.map C.Φ.toLinearMap - X.map (tildePhi C.Φ).toLinearMap‖ ≤ 12 * C.η * ‖X‖ := by
  have := tildePhi_sub_cb C.hF C.hΦ C.hcb C.hη C.hη8 n X
  rw [amp_sub_fun] at this
  rw [norm_sub_rev]; exact this

theorem tilde_cb : CBBound (tildePhi C.Φ).toLinearMap (1 + 12 * C.η) := by
  have := (cb_of_ucp C.hF C.hΦ).add (tildePhi_sub_cb C.hF C.hΦ C.hcb C.hη C.hη8)
  simpa using this

/-- The constant of (12.34). -/
def e34 : ℝ := 12 * C.η + (1 + 12 * C.η) * C.e + C.e

theorem e34_nonneg : 0 ≤ C.e34 := by
  have := C.hη; have := C.he; unfold e34; positivity

/-- **(12.34)** `‖Φ Δ - Δ‖_cb ≤ e34`. -/
theorem phi_delta_cb : CBBound (C.Φ.toLinearMap ∘ₗ C.Δ - C.Δ) C.e34 := by
  have e1 : C.Φ.toLinearMap ∘ₗ C.Δ - C.Δ = (C.Φ.toLinearMap - (tildePhi C.Φ).toLinearMap) ∘ₗ C.Δ
      + (tildePhi C.Φ).toLinearMap ∘ₗ (C.Δ - C.v) + (C.v - C.Δ) := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, C.tilde_comp_v]
    abel
  rw [e1]
  have h1 : CBBound (C.Φ.toLinearMap - (tildePhi C.Φ).toLinearMap) (12 * C.η) := fun n X => by
    rw [amp_sub_fun]; exact C.phi_tilde_close X
  have h2 := h1.comp (by have := C.hη; positivity) C.delta_cb
  have h3 := C.tilde_cb.comp (by have := C.hη; positivity) C.hΔv
  have h4 : CBBound (C.v - C.Δ) C.e := fun n X => by
    rw [amp_sub_fun, norm_sub_rev, ← amp_sub_fun]; exact C.hΔv n X
  have := (h2.add h3).add h4
  simpa [e34, mul_one] using this

theorem pair_sub {A : Type*} [NormedRing A] (a b a₁ b₁ : A) :
    ‖a * b - a₁ * b₁‖ ≤ ‖a - a₁‖ * ‖b‖ + ‖a₁‖ * ‖b - b₁‖ := by
  have e : a * b - a₁ * b₁ = (a - a₁) * b + a₁ * (b - b₁) := by noncomm_ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

theorem triple_sub {A : Type*} [NormedRing A] (a b c a₁ b₁ c₁ : A) :
    ‖a * b * c - a₁ * b₁ * c₁‖ ≤ ‖a - a₁‖ * ‖b‖ * ‖c‖ + ‖a₁‖ * ‖b - b₁‖ * ‖c‖
      + ‖a₁‖ * ‖b₁‖ * ‖c - c₁‖ := by
  have e : a * b * c - a₁ * b₁ * c₁ = (a - a₁) * b * c + a₁ * (b - b₁) * c + a₁ * b₁ * (c - c₁) := by
    noncomm_ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

/-- The constant of (12.35). -/
def e35 : ℝ := 12 * C.η + (1 + 12 * C.η) * (C.e + (1 + C.δ) * C.e) + C.δ + C.e

theorem e35_nonneg : 0 ≤ C.e35 := by
  have := C.hη; have := C.he; have := C.hδ; unfold e35; positivity

set_option maxHeartbeats 1000000 in
/-- **(12.35)** `‖Φₙ(Δₙ(X) Δₙ(Y)) - Δₙ(XY)‖ ≤ e35 ‖X‖ ‖Y‖`. -/
theorem mul35 {n : ℕ} (X Y : Mat n (BlockAlg C.d)) :
    ‖(X.map C.Δ * Y.map C.Δ).map C.Φ.toLinearMap - (X * Y).map C.Δ‖ ≤ C.e35 * ‖X‖ * ‖Y‖ := by
  set a := X.map C.Δ
  set b := Y.map C.Δ
  set a' := X.map C.v
  set b' := Y.map C.v
  have hXn := norm_nonneg X
  have hYn := norm_nonneg Y
  have ha : ‖a‖ ≤ ‖X‖ := by simpa using C.delta_cb n X
  have hb : ‖b‖ ≤ ‖Y‖ := by simpa using C.delta_cb n Y
  have ha' : ‖a'‖ ≤ (1 + C.δ) * ‖X‖ := v_cb C.hv n X
  have hda : ‖a - a'‖ ≤ C.e * ‖X‖ := by rw [← amp_sub_fun]; exact C.hΔv n X
  have hdb : ‖b - b'‖ ≤ C.e * ‖Y‖ := by rw [← amp_sub_fun]; exact C.hΔv n Y
  have hab : ‖a * b‖ ≤ ‖X‖ * ‖Y‖ :=
    (norm_mul_le a b).trans (mul_le_mul ha hb (norm_nonneg b) hXn)
  have T1 := C.phi_tilde_close (a * b)
  have T2 : ‖(a * b).map (tildePhi C.Φ).toLinearMap - (a' * b').map (tildePhi C.Φ).toLinearMap‖
      ≤ (1 + 12 * C.η) * (C.e * ‖X‖ * ‖Y‖ + (1 + C.δ) * ‖X‖ * (C.e * ‖Y‖)) := by
    rw [← amp_sub]
    have h1η : 0 ≤ 1 + 12 * C.η := by linarith [C.hη]
    refine (C.tilde_cb n _).trans (mul_le_mul_of_nonneg_left ?_ h1η)
    refine (pair_sub a b a' b').trans (add_le_add ?_ ?_)
    · exact mul_le_mul hda hb (norm_nonneg b) (mul_nonneg C.he hXn)
    · exact mul_le_mul ha' hdb (norm_nonneg (b - b')) (mul_nonneg (by linarith [C.hδ]) hXn)
  have T3 : ‖(a' * b').map (tildePhi C.Φ).toLinearMap - (X * Y).map C.v‖ ≤ C.δ * ‖X‖ * ‖Y‖ :=
    v_mul C.hv X Y
  have T4 : ‖(X * Y).map C.v - (X * Y).map C.Δ‖ ≤ C.e * (‖X‖ * ‖Y‖) := by
    rw [norm_sub_rev, ← amp_sub_fun]
    exact (C.hΔv n _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) C.he)
  have hη := C.hη
  have e12 : 12 * C.η * ‖a * b‖ ≤ 12 * C.η * (‖X‖ * ‖Y‖) :=
    mul_le_mul_of_nonneg_left hab (by linarith [C.hη])
  calc ‖(a * b).map C.Φ.toLinearMap - (X * Y).map C.Δ‖
      ≤ ‖(a * b).map C.Φ.toLinearMap - (a * b).map (tildePhi C.Φ).toLinearMap‖
        + ‖(a * b).map (tildePhi C.Φ).toLinearMap - (a' * b').map (tildePhi C.Φ).toLinearMap‖
        + ‖(a' * b').map (tildePhi C.Φ).toLinearMap - (X * Y).map C.v‖
        + ‖(X * Y).map C.v - (X * Y).map C.Δ‖ := by
          refine (norm_sub_le_norm_sub_add_norm_sub _ ((X * Y).map C.v) _).trans
            (add_le_add ?_ le_rfl)
          refine (norm_sub_le_norm_sub_add_norm_sub _ ((a' * b').map (tildePhi C.Φ).toLinearMap) _).trans
            (add_le_add ?_ le_rfl)
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C.e35 * ‖X‖ * ‖Y‖ := by unfold e35; nlinarith

/-- The constant of (12.36). -/
def e36 (c₂ : ℝ) : ℝ := 6 * C.e34 + c₂ * C.η + 2 * C.e35

set_option maxHeartbeats 2000000 in
/-- **(12.36)** `‖Φₙ(Δₙ(X) Δₙ(Y) Δₙ(Z)) - Δₙ(XYZ)‖ ≤ e36 ‖X‖‖Y‖‖Z‖`, from (12.6). -/
theorem mul36 {c₂ : ℝ} (hc₂ : 0 ≤ c₂) {n : ℕ}
    (hK2 : ∀ X' Y' Z' : Mat n (H →L[ℂ] H),
      ‖(((X'.map C.Φ * Y'.map C.Φ).map C.Φ) * Z'.map C.Φ).map C.Φ
        - (X'.map C.Φ * Y'.map C.Φ * Z'.map C.Φ).map C.Φ‖ ≤ c₂ * C.η * ‖X'‖ * ‖Y'‖ * ‖Z'‖)
    (X Y Z : Mat n (BlockAlg C.d)) :
    ‖(X.map C.Δ * Y.map C.Δ * Z.map C.Δ).map C.Φ.toLinearMap - (X * Y * Z).map C.Δ‖
      ≤ C.e36 c₂ * ‖X‖ * ‖Y‖ * ‖Z‖ := by
  set a := X.map C.Δ
  set b := Y.map C.Δ
  set c := Z.map C.Δ
  set fa := a.map C.Φ.toLinearMap
  set fb := b.map C.Φ.toLinearMap
  set fc := c.map C.Φ.toLinearMap
  have hXn := norm_nonneg X
  have hYn := norm_nonneg Y
  have hZn := norm_nonneg Z
  have e34n := C.e34_nonneg
  have e35n := C.e35_nonneg
  have ha : ‖a‖ ≤ ‖X‖ := by simpa using C.delta_cb n X
  have hb : ‖b‖ ≤ ‖Y‖ := by simpa using C.delta_cb n Y
  have hc : ‖c‖ ≤ ‖Z‖ := by simpa using C.delta_cb n Z
  have hfa : ‖fa‖ ≤ ‖X‖ := by have h := C.phi_cb n a; rw [one_mul] at h; exact h.trans ha
  have hfb : ‖fb‖ ≤ ‖Y‖ := by have h := C.phi_cb n b; rw [one_mul] at h; exact h.trans hb
  have hfc : ‖fc‖ ≤ ‖Z‖ := by have h := C.phi_cb n c; rw [one_mul] at h; exact h.trans hc
  have hda : ‖a - fa‖ ≤ C.e34 * ‖X‖ := by
    rw [norm_sub_rev]; have := C.phi_delta_cb n X; rwa [amp_sub_fun, amp_comp] at this
  have hdb : ‖b - fb‖ ≤ C.e34 * ‖Y‖ := by
    rw [norm_sub_rev]; have := C.phi_delta_cb n Y; rwa [amp_sub_fun, amp_comp] at this
  have hdc : ‖c - fc‖ ≤ C.e34 * ‖Z‖ := by
    rw [norm_sub_rev]; have := C.phi_delta_cb n Z; rwa [amp_sub_fun, amp_comp] at this
  -- S1
  have S1 : ‖(a * b * c).map C.Φ.toLinearMap - (fa * fb * fc).map C.Φ.toLinearMap‖
      ≤ 3 * C.e34 * ‖X‖ * ‖Y‖ * ‖Z‖ := by
    rw [← amp_sub]
    have h0 := C.phi_cb n (a * b * c - fa * fb * fc)
    rw [one_mul] at h0
    refine h0.trans ?_
    refine (triple_sub a b c fa fb fc).trans ?_
    have t1 : ‖a - fa‖ * ‖b‖ * ‖c‖ ≤ C.e34 * ‖X‖ * ‖Y‖ * ‖Z‖ :=
      mul_le_mul (mul_le_mul hda hb (norm_nonneg b) (mul_nonneg e34n hXn)) hc (norm_nonneg c)
        (mul_nonneg (mul_nonneg e34n hXn) hYn)
    have t2 : ‖fa‖ * ‖b - fb‖ * ‖c‖ ≤ ‖X‖ * (C.e34 * ‖Y‖) * ‖Z‖ :=
      mul_le_mul (mul_le_mul hfa hdb (norm_nonneg (b - fb)) hXn) hc (norm_nonneg c)
        (mul_nonneg hXn (mul_nonneg e34n hYn))
    have t3 : ‖fa‖ * ‖fb‖ * ‖c - fc‖ ≤ ‖X‖ * ‖Y‖ * (C.e34 * ‖Z‖) :=
      mul_le_mul (mul_le_mul hfa hfb (norm_nonneg fb) hXn) hdc (norm_nonneg (c - fc))
        (mul_nonneg hXn hYn)
    nlinarith
  -- S2 (Kitaev (12.6))
  have hcη : 0 ≤ c₂ * C.η := mul_nonneg hc₂ C.hη
  have S2 : ‖((fa * fb).map C.Φ.toLinearMap * fc).map C.Φ.toLinearMap - (fa * fb * fc).map C.Φ.toLinearMap‖
      ≤ c₂ * C.η * ‖X‖ * ‖Y‖ * ‖Z‖ := by
    refine (hK2 a b c).trans ?_
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left ha hcη) hb (norm_nonneg b)
      (mul_nonneg hcη hXn)) hc (norm_nonneg c) (mul_nonneg (mul_nonneg hcη hXn) hYn)
  -- S3
  have hab : ‖a * b‖ ≤ ‖X‖ * ‖Y‖ := (norm_mul_le a b).trans (mul_le_mul ha hb (norm_nonneg b) hXn)
  have hfab : ‖fa * fb - a * b‖ ≤ 2 * C.e34 * ‖X‖ * ‖Y‖ := by
    refine (pair_sub fa fb a b).trans ?_
    have t1 : ‖fa - a‖ * ‖fb‖ ≤ C.e34 * ‖X‖ * ‖Y‖ := by
      rw [norm_sub_rev]; exact mul_le_mul hda hfb (norm_nonneg fb) (mul_nonneg e34n hXn)
    have t2 : ‖a‖ * ‖fb - b‖ ≤ ‖X‖ * (C.e34 * ‖Y‖) := by
      rw [norm_sub_rev]; exact mul_le_mul ha hdb (norm_nonneg (b - fb)) hXn
    nlinarith
  have S3 : ‖((fa * fb).map C.Φ.toLinearMap * fc).map C.Φ.toLinearMap
      - ((a * b).map C.Φ.toLinearMap * c).map C.Φ.toLinearMap‖ ≤ 3 * C.e34 * ‖X‖ * ‖Y‖ * ‖Z‖ := by
    rw [← amp_sub]
    have h0 := C.phi_cb n ((fa * fb).map C.Φ.toLinearMap * fc
      - (a * b).map C.Φ.toLinearMap * c)
    rw [one_mul] at h0
    refine h0.trans ?_
    refine (pair_sub _ fc _ c).trans ?_
    have u1 : ‖(fa * fb).map C.Φ.toLinearMap - (a * b).map C.Φ.toLinearMap‖ ≤ 2 * C.e34 * ‖X‖ * ‖Y‖ := by
      rw [← amp_sub]
      have h0 := C.phi_cb n (fa * fb - a * b)
      rw [one_mul] at h0
      exact h0.trans hfab
    have u2 : ‖(a * b).map C.Φ.toLinearMap‖ ≤ ‖X‖ * ‖Y‖ := by
      have h0 := C.phi_cb n (a * b)
      rw [one_mul] at h0
      exact h0.trans hab
    have u3 : ‖fc - c‖ ≤ C.e34 * ‖Z‖ := by rw [norm_sub_rev]; exact hdc
    have v1 := mul_le_mul u1 hfc (norm_nonneg fc)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) e34n) hXn) hYn)
    have v2 := mul_le_mul u2 u3 (norm_nonneg (fc - c)) (mul_nonneg hXn hYn)
    nlinarith
  -- S4
  have S4 : ‖((a * b).map C.Φ.toLinearMap * c).map C.Φ.toLinearMap
      - ((X * Y).map C.Δ * c).map C.Φ.toLinearMap‖ ≤ C.e35 * ‖X‖ * ‖Y‖ * ‖Z‖ := by
    rw [← amp_sub, ← sub_mul]
    have h0 := C.phi_cb n (((a * b).map C.Φ.toLinearMap - (X * Y).map C.Δ) * c)
    rw [one_mul] at h0
    refine h0.trans ?_
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_mul (C.mul35 X Y) hc (norm_nonneg c) (mul_nonneg (mul_nonneg e35n hXn) hYn)
  -- S5
  have S5 : ‖((X * Y).map C.Δ * c).map C.Φ.toLinearMap - (X * Y * Z).map C.Δ‖
      ≤ C.e35 * ‖X‖ * ‖Y‖ * ‖Z‖ := by
    refine (C.mul35 (X * Y) Z).trans ?_
    have hxy : ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := norm_mul_le X Y
    have := mul_le_mul_of_nonneg_left hxy e35n
    nlinarith [mul_le_mul_of_nonneg_right this hZn]
  have key : (a * b * c).map C.Φ.toLinearMap - (X * Y * Z).map C.Δ =
      ((a * b * c).map C.Φ.toLinearMap - (fa * fb * fc).map C.Φ.toLinearMap)
      - (((fa * fb).map C.Φ.toLinearMap * fc).map C.Φ.toLinearMap - (fa * fb * fc).map C.Φ.toLinearMap)
      + (((fa * fb).map C.Φ.toLinearMap * fc).map C.Φ.toLinearMap
          - ((a * b).map C.Φ.toLinearMap * c).map C.Φ.toLinearMap)
      + (((a * b).map C.Φ.toLinearMap * c).map C.Φ.toLinearMap
          - ((X * Y).map C.Δ * c).map C.Φ.toLinearMap)
      + (((X * Y).map C.Δ * c).map C.Φ.toLinearMap - (X * Y * Z).map C.Δ) := by abel
  rw [key]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)) le_rfl).trans ?_
  unfold e36
  nlinarith

end Ctx



end Cert.KitaevChannels
