import Certs.KitaevChannels.Plumbing
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# `Φ̃ = θ(2Φ-1)`: summability and `‖Φ̃ - Φ‖_cb ≤ 12 η`

Kitaev states `‖Φ̃ - Φ‖_cb ≤ O(η)` (after (12.2)); we prove it with the constant `12` for
`η ≤ 1/8`, from `‖Φ‖_cb ≤ 1` and the bound `(2k choose k) ≤ 4ᵏ`.
-/

open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace Cert.KitaevChannels

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `X ↦ X.map T` as a continuous linear map of `T`. -/
def evMat {n : ℕ} (X : Mat n (H →L[ℂ] H)) :
    ((H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) →L[ℂ] Mat n (H →L[ℂ] H) where
  toFun T := X.map T
  map_add' S T := by ext i j; rfl
  map_smul' c T := by ext i j; rfl
  cont := by
    show Continuous fun T : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) => (fun i j => T (X i j) : Matrix _ _ _)
    exact continuous_pi fun i => continuous_pi fun j =>
      (ContinuousLinearMap.apply ℂ (H →L[ℂ] H) (X i j)).continuous

theorem opNorm_le_of_cb {T : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)} {c : ℝ} (hc : 0 ≤ c)
    (h : CBBound T.toLinearMap c) : ‖T‖ ≤ c :=
  T.opNorm_le_bound hc fun x => h.apply_le x

theorem CBBound.tsum {a : ℕ → (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)} {b : ℕ → ℝ} {B : ℝ}
    (hb : HasSum b B) (hb0 : ∀ k, 0 ≤ b k) (h : ∀ k, CBBound (a k).toLinearMap (b k)) :
    Summable a ∧ CBBound (∑' k, a k).toLinearMap B := by
  have hs : Summable a := Summable.of_norm_bounded hb.summable fun k => opNorm_le_of_cb (hb0 k) (h k)
  refine ⟨hs, fun n X => ?_⟩
  have e : X.map (∑' k, a k).toLinearMap = ∑' k, X.map (a k).toLinearMap :=
    (evMat X).map_tsum hs
  rw [e]
  exact tsum_of_norm_bounded (hb.mul_right ‖X‖) fun k => h k n X

/-- `Nᵏ` is cb-bounded by `cᵏ` if `N` is cb-bounded by `c ≥ 0`. -/
theorem CBBound.pow {N : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)} {c : ℝ} (hc : 0 ≤ c)
    (h : CBBound N.toLinearMap c) (k : ℕ) : CBBound (N ^ k).toLinearMap (c ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact CBBound.id
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact ih.comp (pow_nonneg hc k) h

/-- The central binomial coefficients of `(1-x)^{-1/2}`. -/
def cbin (k : ℕ) : ℂ := (Nat.centralBinom k : ℂ) / 4 ^ k

theorem norm_cbin_le (k : ℕ) : ‖cbin k‖ ≤ 1 := by
  rw [cbin, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_ofNat]
  rw [div_le_one (by positivity)]
  exact_mod_cast Nat.centralBinom_le_four_pow k

/-- The algebra behind `Φ̃ - Φ = (Φ - ½)·S'`. -/
theorem half_identity {R : Type*} [Ring R] [Algebra ℂ R] (x s : R) :
    (1 / 2 : ℂ) • (1 + (2 • x - 1) * (1 + s)) - x = (x - (1 / 2 : ℂ) • 1) * s := by
  rw [two_nsmul]
  simp only [mul_add, mul_one, add_mul, sub_mul, smul_add, smul_sub, smul_mul_assoc, one_mul]
  module

theorem cbin_zero : cbin 0 = 1 := by simp [cbin]

theorem N_eq (Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) :
    (4 • (Φ - Φ * Φ) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) = (-4 : ℂ) • (Φ * Φ - Φ) := by
  rw [← Nat.cast_smul_eq_nsmul ℂ]; module

theorem N_cb {Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)} {η : ℝ}
    (hcb : CBBound (Φ * Φ - Φ).toLinearMap η) :
    CBBound (4 • (Φ - Φ * Φ) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)).toLinearMap (4 * η) := by
  rw [N_eq]
  have := hcb.smul (-4 : ℂ)
  rwa [norm_neg, Complex.norm_ofNat] at this

/-- Splitting off the `k = 0` term of the series. -/
theorem series_split (N : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (hS : Summable fun k => cbin k • N ^ k) :
    (∑' k, cbin k • N ^ k) = 1 + ∑' k, cbin (k + 1) • N ^ (k + 1) := by
  rw [hS.tsum_eq_zero_add, cbin_zero, pow_zero, one_smul]

theorem tildePhi_eq (Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) :
    tildePhi Φ = (1 / 2 : ℂ) • (1 + (2 • Φ - 1) *
      ∑' k, cbin k • (4 • (Φ - Φ * Φ) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) ^ k) := rfl

variable (hF : CPMapFacts)
include hF

set_option maxHeartbeats 2000000 in
/-- **Kitaev, after (12.2)**: `‖Φ̃ - Φ‖_cb ≤ 12 η` for an η-idempotent UCP map with `η ≤ 1/8`. -/
theorem tildePhi_sub_cb [Nontrivial H] {Φ : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)} {η : ℝ}
    (hΦ : IsUCP Φ.toLinearMap) (hcb : CBBound (Φ * Φ - Φ).toLinearMap η) (hη : 0 ≤ η)
    (hη8 : η ≤ 1 / 8) :
    CBBound ((tildePhi Φ).toLinearMap - Φ.toLinearMap) (12 * η) := by
  obtain ⟨N, hN⟩ : ∃ N : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H), N = 4 • (Φ - Φ * Φ) := ⟨_, rfl⟩
  have hNcb : CBBound N.toLinearMap (4 * η) := hN ▸ N_cb hcb
  have h4η : 0 ≤ 4 * η := by positivity
  have h4η1 : 4 * η < 1 := by linarith
  have hΦcb : CBBound Φ.toLinearMap 1 := cb_of_ucp hF hΦ
  obtain ⟨P, hP⟩ : ∃ P : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H), P = Φ - (1 / 2 : ℂ) • 1 := ⟨_, rfl⟩
  have hPcb : CBBound P.toLinearMap (3 / 2) := by
    have h := hΦcb.sub ((CBBound.id (M₁ := H →L[ℂ] H)).smul (1 / 2 : ℂ))
    have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hn] at h
    rw [hP]
    exact h.mono (by norm_num)
  have hterm : ∀ k, CBBound (cbin k • N ^ k).toLinearMap ((4 * η) ^ k) := fun k => by
    have h := (hNcb.pow h4η k).smul (cbin k)
    refine h.mono ?_
    have := norm_cbin_le k
    have : 0 ≤ (4 * η) ^ k := pow_nonneg h4η k
    nlinarith
  have hS : Summable fun k => cbin k • N ^ k :=
    (CBBound.tsum (hasSum_geometric_of_lt_one h4η h4η1) (fun k => pow_nonneg h4η k) hterm).1
  have hS' : Summable fun k => cbin (k + 1) • N ^ (k + 1) := (summable_nat_add_iff 1).2 hS
  have hdiff : tildePhi Φ - Φ = P * ∑' k, cbin (k + 1) • N ^ (k + 1) := by
    rw [tildePhi_eq, ← hN, series_split N hS, hP]
    exact half_identity Φ _
  have hsum : P * (∑' k, cbin (k + 1) • N ^ (k + 1)) =
      ∑' k, P * (cbin (k + 1) • N ^ (k + 1)) :=
    (hS'.tsum_mul_left _).symm
  have hterm' : ∀ k, CBBound (P * (cbin (k + 1) • N ^ (k + 1))).toLinearMap
      (6 * η * (4 * η) ^ k) := fun k => by
    have h := hPcb.comp (by norm_num) (hterm (k + 1))
    refine h.mono ?_
    rw [pow_succ]; nlinarith [pow_nonneg h4η k]
  have hb : HasSum (fun k => 6 * η * (4 * η) ^ k) (6 * η * (1 - 4 * η)⁻¹) :=
    (hasSum_geometric_of_lt_one h4η h4η1).mul_left (6 * η)
  have hfin := (CBBound.tsum hb (fun k => by positivity) hterm').2
  rw [← hsum, ← hdiff] at hfin
  have h12 : (1 - 4 * η)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  exact hfin.mono (by nlinarith)

end Cert.KitaevChannels
