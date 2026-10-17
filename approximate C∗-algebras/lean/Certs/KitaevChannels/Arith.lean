import Mathlib.Tactic

/-!
# The explicit constants of Theorem A

With `x = Λη ≤ 1/200000`, `Λ ≥ 1`, `δ ≤ x`, `η ≤ x`, `c₂η ≤ x`, every error term of §12 is at most
an explicit multiple of `x`. Pure real arithmetic.
-/

namespace Cert.KitaevChannels

theorem arith_delta {x η δ : ℝ} (hη : 0 ≤ η) (hηx : η ≤ x) (hδ0 : 0 ≤ δ) (hδ : δ ≤ x)
    (hs : x ≤ 1 / 200000) :
    12 * η * (1 + δ) ^ 2 + δ + δ ≤ 1 / 2 ∧
    2 * (12 * η * (1 + δ) ^ 2 + δ + δ) * (2 + 2 * (12 * η * (1 + δ) ^ 2 + δ + δ))
      * (1 + δ + (12 * η * (1 + δ) ^ 2 + δ)) + (12 * η * (1 + δ) ^ 2 + δ) ≤ 200 * x := by
  have hδδ : δ * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right (by linarith) hδ0
  have hsq : (1 + δ) ^ 2 ≤ 1001 / 1000 := by nlinarith
  have hK : 12 * η * (1 + δ) ^ 2 + δ ≤ 14 * x := by
    have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 12 * η)
    linarith
  have hK0 : 0 ≤ 12 * η * (1 + δ) ^ 2 + δ := by positivity
  set K := 12 * η * (1 + δ) ^ 2 + δ
  have ht : K + δ ≤ 15 * x := by linarith
  refine ⟨by linarith, ?_⟩
  set t := K + δ
  have ht0 : 0 ≤ t := by positivity
  have h3 : 1 + δ + K ≤ 2 := by linarith
  have htt : t * t ≤ (1 / 2) * t := mul_le_mul_of_nonneg_right (by linarith) ht0
  have h4 : 2 * t * (2 + 2 * t) ≤ 6 * t := by nlinarith
  have h5 : 0 ≤ 2 * t * (2 + 2 * t) := by positivity
  have h6 : 2 * t * (2 + 2 * t) * (1 + δ + K) ≤ 6 * t * 2 :=
    mul_le_mul h4 h3 (by positivity) (by positivity)
  linarith

theorem arith_main {x η δ e c₂ e34 e35 e36 κ u q t' Q : ℝ} (hη : 0 ≤ η) (hηx : η ≤ x)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ x) (hc₂ : 0 ≤ c₂) (hc₂x : c₂ * η ≤ x) (he0 : 0 ≤ e)
    (he : e ≤ 200 * x) (hs : x ≤ 1 / 200000)
    (h34 : e34 = 12 * η + (1 + 12 * η) * e + e)
    (h35 : e35 = 12 * η + (1 + 12 * η) * (e + (1 + δ) * e) + δ + e)
    (h36 : e36 = 6 * e34 + c₂ * η + 2 * e35)
    (hκ : κ = 4 * (e34 + e36) + 2 * (δ + e + e35 + η))
    (hu : u = (1 + 12 * η) / (1 - δ))
    (hq : q = η + 12 * η + e * u + κ * u)
    (ht' : t' = q + δ / (1 - δ))
    (hQ : Q = 2 * t' * (2 + 2 * t') + q) :
    0 ≤ κ ∧ t' ≤ 1 / 2 ∧ 0 ≤ Q ∧ Q ≤ 264000 * x ∧
      (12 * η + e35 + e) / (1 - δ) ≤ 1700 * x := by
  have hx0 : 0 ≤ x := hη.trans hηx
  have hd1 : 0 < 1 - δ := by linarith
  have hηe : η * e ≤ (1 / 10000) * e := mul_le_mul_of_nonneg_right (by linarith) he0
  have hδe : δ * e ≤ (1 / 10000) * e := mul_le_mul_of_nonneg_right (by linarith) he0
  have hηδ : η * δ ≤ (1 / 10000) * 1 := mul_le_mul (by linarith) (by linarith) hδ0 (by norm_num)
  have hηδe : η * δ * e ≤ (1 / 10000 * 1) * e := mul_le_mul_of_nonneg_right hηδ he0
  have e34b : e34 ≤ 420 * x := by rw [h34]; linarith
  have e34n : 0 ≤ e34 := by rw [h34]; positivity
  have e35b : e35 ≤ 620 * x := by rw [h35]; linarith
  have e35n : 0 ≤ e35 := by rw [h35]; positivity
  have e36b : e36 ≤ 3800 * x := by rw [h36]; linarith
  have e36n : 0 ≤ e36 := by rw [h36]; positivity
  have κb : κ ≤ 18600 * x := by rw [hκ]; linarith
  have κn : 0 ≤ κ := by rw [hκ]; positivity
  have ub : u ≤ 2 := by rw [hu, div_le_iff₀ hd1]; linarith
  have un : 0 ≤ u := by rw [hu]; exact div_nonneg (by linarith) hd1.le
  have qb : q ≤ 37700 * x := by
    rw [hq]
    have h1 := mul_le_mul he ub un (by positivity)
    have h2 := mul_le_mul κb ub un (by positivity)
    linarith
  have qn : 0 ≤ q := by rw [hq]; positivity
  have hδδ : δ * δ ≤ (1 / 2) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ0
  have hδd : δ / (1 - δ) ≤ 2 * δ := by rw [div_le_iff₀ hd1]; linarith
  have hδdn : 0 ≤ δ / (1 - δ) := div_nonneg hδ0 hd1.le
  have t'b : t' ≤ 37702 * x := by rw [ht']; linarith
  have t'n : 0 ≤ t' := by rw [ht']; positivity
  have t'h : t' ≤ 1 / 2 := by linarith
  refine ⟨κn, t'h, by rw [hQ]; positivity, ?_, ?_⟩
  · rw [hQ]
    have htt : t' * t' ≤ (1 / 2) * t' := mul_le_mul_of_nonneg_right t'h t'n
    have : 2 * t' * (2 + 2 * t') ≤ 6 * t' := by linarith
    linarith
  · rw [div_le_iff₀ hd1]
    have hxδ : x * δ ≤ x * (1 / 200000) := mul_le_mul_of_nonneg_left (by linarith) hx0
    linarith

end Cert.KitaevChannels
