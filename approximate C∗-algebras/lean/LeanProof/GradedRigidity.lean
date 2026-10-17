import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Graded rigidity of small associators (note, Proposition 4.3)

Let `c : G → G → ℝ` be a real 2-cochain on a group and `β = d c` its coboundary. The twisted
group algebra `e_g ⋆ e_h = exp(i t c(g,h)) e_{gh}` has associator phase `exp(-i t β)`, which is
uniformly small when `t ‖β‖_∞` is small. We prove: if some *associative* `U(1)`-twist `σ`
(a `U(1)`-valued 2-cocycle) is uniformly within `‖exp(iπ/4) - 1‖ = 2 sin(π/8)` of
`exp(i t c)`, and `|t β| < π`, then `β` is the coboundary of a *bounded* 2-cochain,
i.e. `[β] = 0` in bounded cohomology `H³_b(G; ℝ)`.

Contrapositive: a bounded 3-cocycle whose class in `H³_b` is nonzero, but which is the coboundary
of an unbounded 2-cochain, gives arbitrarily small associators that no graded associative twist
can approximate.
-/

open Complex

noncomputable section

namespace Kitaev.Graded

variable {G : Type*} [Group G]

/-- Inhomogeneous coboundary of a real 2-cochain. -/
def d2 (c : G → G → ℝ) (g h k : G) : ℝ := c h k - c (g * h) k + c g (h * k) - c g h

/-- `σ` is a `U(1)`-valued 2-cocycle, i.e. `e_g ⋆ e_h = σ(g,h) e_{gh}` is associative. -/
def IsU1Cocycle (σ : G → G → ℂ) : Prop :=
  (∀ g h, ‖σ g h‖ = 1) ∧ ∀ g h k, σ h k * σ g (h * k) = σ g h * σ (g * h) k

/-- A unit complex number `exp(iγ)` with `γ ∈ (-π, π]` and `‖exp(iγ) - 1‖ < ‖exp(iπ/4) - 1‖`
has `|γ| < π/4`. -/
theorem abs_lt_of_norm_exp_sub_one_lt {γ : ℝ} (h1 : -Real.pi < γ) (h2 : γ ≤ Real.pi)
    (h : ‖exp (I * γ) - 1‖ < ‖exp (I * ↑(Real.pi / 4)) - 1‖) : |γ| < Real.pi / 4 := by
  rw [norm_exp_I_mul_ofReal_sub_one, norm_exp_I_mul_ofReal_sub_one] at h
  simp only [norm_mul, Real.norm_eq_abs, abs_two] at h
  have hs : |Real.sin (γ / 2)| < |Real.sin (Real.pi / 4 / 2)| := by linarith
  have hpos : 0 < Real.sin (Real.pi / 4 / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  rw [abs_of_pos hpos] at hs
  -- `|sin (γ/2)| = sin |γ/2|` since `|γ/2| ≤ π/2`
  have hγ2 : |γ / 2| ≤ Real.pi / 2 := by
    rw [abs_le]; constructor <;> linarith
  have key : Real.sin |γ / 2| < Real.sin (Real.pi / 4 / 2) := by
    rcases le_total 0 (γ / 2) with hg | hg
    · rw [abs_of_nonneg hg]; rwa [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hg
        (by linarith [abs_le.1 hγ2]))] at hs
    · rw [abs_of_nonpos hg, Real.sin_neg]
      rwa [abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le hg
        (by linarith [abs_le.1 hγ2]))] at hs
  have hlt : |γ / 2| < Real.pi / 4 / 2 := by
    by_contra hcon
    push Not at hcon
    have := Real.strictMonoOn_sin.monotoneOn
      (show Real.pi / 4 / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [Real.pi_pos])
      (show |γ / 2| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [abs_nonneg (γ / 2)]) hcon
    linarith
  rw [abs_div, abs_two] at hlt
  linarith

theorem graded_rigidity (c : G → G → ℝ) (t : ℝ) (ht : 0 < t)
    (hβ : ∀ g h k, |t * d2 c g h k| < Real.pi)
    (σ : G → G → ℂ) (hσ : IsU1Cocycle σ)
    (hclose : ∀ g h, ‖exp (I * ↑(t * c g h)) - σ g h‖ < ‖exp (I * ↑(Real.pi / 4)) - 1‖) :
    ∃ b : G → G → ℝ, (∀ g h, |b g h| ≤ Real.pi / (4 * t)) ∧ d2 b = d2 c := by
  obtain ⟨hσ1, hσc⟩ := hσ
  have hσ0 : ∀ g h, σ g h ≠ 0 := fun g h hz => by simpa [hz] using hσ1 g h
  -- the ratio `w = exp(itc)/σ` and its argument `γ`
  set w : G → G → ℂ := fun g h => exp (I * ↑(t * c g h)) / σ g h with hw
  set γ : G → G → ℝ := fun g h => arg (w g h) with hγ
  have hw1 : ∀ g h, ‖w g h‖ = 1 := fun g h => by
    simp only [hw, norm_div, hσ1, div_one]
    rw [mul_comm]; exact norm_exp_ofReal_mul_I _
  have hexpγ : ∀ g h, exp (I * ↑(γ g h)) = w g h := fun g h => by
    have := norm_mul_exp_arg_mul_I (w g h)
    rw [hw1, ofReal_one, one_mul] at this
    rw [mul_comm]; exact this
  have hγsmall : ∀ g h, |γ g h| < Real.pi / 4 := fun g h => by
    apply abs_lt_of_norm_exp_sub_one_lt (neg_pi_lt_arg _) (arg_le_pi _)
    rw [hexpγ]
    have e : w g h - 1 = (exp (I * ↑(t * c g h)) - σ g h) / σ g h := by
      simp only [hw]; field_simp [hσ0 g h]
    rw [e, norm_div, hσ1, div_one]
    exact hclose g h
  -- `τ = t c - γ` lifts `σ`
  set τ : G → G → ℝ := fun g h => t * c g h - γ g h with hτ
  have hστ : ∀ g h, σ g h = exp (I * ↑(τ g h)) := fun g h => by
    have h1 : exp (I * ↑(τ g h)) = exp (I * ↑(t * c g h)) / exp (I * ↑(γ g h)) := by
      rw [← Complex.exp_sub]; congr 1; simp [hτ]; ring
    rw [h1, hexpγ]; simp only [hw]; field_simp [hσ0 g h]
  -- the cocycle identity forces `d τ ∈ 2πℤ`, hence `d τ = 0`
  have hdτ : ∀ g h k, d2 τ g h k = 0 := fun g h k => by
    have hc := hσc g h k
    simp only [hστ, ← Complex.exp_add] at hc
    have hc' : exp (I * ↑(d2 τ g h k)) = 1 := by
      have : I * ↑(d2 τ g h k) = (I * ↑(τ h k) + I * ↑(τ g (h * k)))
          - (I * ↑(τ g h) + I * ↑(τ (g * h) k)) := by simp [d2]; ring
      rw [this, Complex.exp_sub, hc, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hc'
    have hn' : d2 τ g h k = n * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      simpa [mul_comm, mul_assoc, mul_left_comm] using this
    have hbound : |d2 τ g h k| < 2 * Real.pi := by
      have e : d2 τ g h k = t * d2 c g h k - d2 γ g h k := by simp [d2, hτ]; ring
      have hγ' : |d2 γ g h k| < Real.pi := by
        have a1 := abs_lt.1 (hγsmall h k); have a2 := abs_lt.1 (hγsmall (g * h) k)
        have a3 := abs_lt.1 (hγsmall g (h * k)); have a4 := abs_lt.1 (hγsmall g h)
        rw [abs_lt]; constructor <;> simp only [d2] <;> linarith
      rw [e]
      calc |t * d2 c g h k - d2 γ g h k| ≤ |t * d2 c g h k| + |d2 γ g h k| := abs_sub _ _
        _ < Real.pi + Real.pi := add_lt_add (hβ g h k) hγ'
        _ = 2 * Real.pi := by ring
    rw [hn'] at hbound ⊢
    have hpi := Real.pi_pos
    have : |(n : ℝ)| < 1 := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hbound
      nlinarith [abs_nonneg (n : ℝ)]
    have hn0 : n = 0 := by
      have h' : |n| < 1 := by exact_mod_cast this
      have := abs_lt.1 h'
      omega
    simp [hn0]
  -- `b = γ / t` is bounded and `d b = d c`
  refine ⟨fun g h => γ g h / t, fun g h => ?_, ?_⟩
  · rw [abs_div, abs_of_pos ht, div_le_div_iff₀ ht (by positivity)]
    nlinarith [hγsmall g h, abs_nonneg (γ g h)]
  · funext g h k
    have e := hdτ g h k
    simp only [d2, hτ] at e ⊢
    field_simp
    linarith

end Kitaev.Graded
