import JanischLehericy.Pair
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FunProp

open scoped BigOperators
open MeasureTheory Finset
noncomputable section
namespace JanischLehericy

def ell (t : ℝ) : ℝ := t^2 * min 1 t

theorem ell_nonneg {t : ℝ} (h : 0 ≤ t) : 0 ≤ ell t := by
  exact mul_nonneg (sq_nonneg _) (le_min zero_le_one h)

theorem ell_le_sq {t : ℝ} : ell t ≤ t^2 :=
  mul_le_of_le_one_right (sq_nonneg _) (min_le_left _ _)

theorem ell_le_rpow {t δ : ℝ} (ht : 0 ≤ t) (h2 : 2 ≤ δ) (h3 : δ ≤ 3) :
    ell t ≤ t ^ δ := by
  rcases le_total t 1 with h | h
  · rw [ell, min_eq_right h, ← pow_succ, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge' ht h (by linarith) h3
  · rw [ell, min_eq_left h, mul_one, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h h2

/-- Scalar estimate for deleting at most two closed neighborhoods. -/
theorem sq_le_truncated {t : ℝ} (ht : 0 ≤ t) :
    t^2 ≤ 1 / 64 + 8 * ell t := by
  by_cases hs : t ≤ 1 / 8
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ 1 / 8 + t by linarith),
        ell_nonneg ht]
  · have hmin : 1 / 8 ≤ min 1 t := le_min (by norm_num) (le_of_not_ge hs)
    nlinarith only [mul_le_mul_of_nonneg_left hmin (sq_nonneg t),
      show ell t = t^2 * min 1 t from rfl]

theorem ell_scale_le {t c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) (hc2 : c ≤ 2) :
    ell (c*t) ≤ 8 * ell t := by
  have hmin : min 1 (c*t) ≤ 2 * min 1 t := by
    rcases le_total t 1 with h | h
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right hc2 ht)
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by norm_num)
  have hpow : (c*t)^2 ≤ 4*t^2 := by
    rw [mul_pow]
    have h : c^2 ≤ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (show 0 ≤ 2+c by linarith)]
    exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
  have h := mul_le_mul hpow hmin (le_min zero_le_one (mul_nonneg hc ht)) (by positivity)
  unfold ell
  linarith only [h]

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
def beta (μ : Measure Ω) (m : ℕ) (X : ι → Ω → ℝ) : ℝ :=
  (∑ i, ∫ ω, ell (m * |X i ω|) ∂μ) / m

theorem beta_nonneg (μ : Measure Ω) (m : ℕ) (X : ι → Ω → ℝ) : 0 ≤ beta μ m X :=
  div_nonneg (sum_nonneg fun _ _ => integral_nonneg fun _ =>
    ell_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))) (Nat.cast_nonneg _)

theorem integrable_ell (μ : Measure Ω) {X : Ω → ℝ} (hX : MemLp X 2 μ) (m : ℕ) :
    Integrable (fun ω => ell (m * |X ω|)) μ := by
  have hsq := hX.integrable_sq.const_mul ((m : ℝ)^2)
  apply hsq.mono'
  · exact (show Continuous (fun t : ℝ => ell (m * |t|)) by unfold ell; fun_prop).comp_aestronglyMeasurable hX.aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (ell_nonneg (by positivity))]
    simpa [mul_pow, sq_abs] using (ell_le_sq (t := (m : ℝ) * |X ω|))

theorem beta_le_delta (μ : Measure Ω) (m : ℕ) (hm : 0 < m)
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    {δ : ℝ} (h2 : 2 < δ) (h3 : δ ≤ 3)
    (hp : ∀ i, Integrable (fun ω => |X i ω| ^ δ) μ) :
    beta μ m X ≤ (m : ℝ) ^ (δ-1) * ∑ i, ∫ ω, |X i ω| ^ δ ∂μ := by
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have h i : (∫ ω, ell (m * |X i ω|) ∂μ) ≤
      (m : ℝ)^δ * ∫ ω, |X i ω|^δ ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono (integrable_ell μ (hX i) m) ((hp i).const_mul _)
    intro ω
    simpa [Real.mul_rpow hm'.le (abs_nonneg _)] using
      (ell_le_rpow (t := (m : ℝ)*|X i ω|) (by positivity) h2.le h3)
  unfold beta
  apply (div_le_iff₀ hm').mpr
  calc
    _ ≤ ∑ i, (m : ℝ)^δ * ∫ ω, |X i ω|^δ ∂μ := sum_le_sum fun i _ => h i
    _ = _ := by rw [← mul_sum, Real.rpow_sub_one hm'.ne']; field_simp

/-- Scalar domination used to replace each marginal by its root mean square. -/
theorem envelope_point {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    t^2 * min 1 s ≤ 2 * ell t + ell s / 4 := by
  rcases le_total t (s/2) with h | h
  · have hsq : t^2 ≤ s^2 / 4 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ s/2+t by linarith)]
    have := mul_le_mul_of_nonneg_right hsq (le_min zero_le_one hs)
    have hn := ell_nonneg ht
    unfold ell at hn ⊢
    linarith only [this, hn]
  · have hm : min 1 s ≤ 2 * min 1 t := by
      rcases le_total t 1 with h' | h'
      · rw [min_eq_right h']; exact (min_le_right _ _).trans (by linarith)
      · rw [min_eq_left h']; exact (min_le_left _ _).trans (by norm_num)
    have := mul_le_mul_of_nonneg_left hm (sq_nonneg t)
    have hn := ell_nonneg hs
    unfold ell at hn ⊢
    linarith only [this, hn]

theorem absorption_constants (β e : ℝ) (hβ : 0 < β)
    (h : e ≤ 2*(50000*β)+10752*β+24576*250000*β^2/(50000*β)) :
    e ≤ 250000*β := by
  have ht : 24576*250000*β^2/(50000*β) = 122880*β := by
    field_simp
    ring
  rw [ht] at h
  linarith

end JanischLehericy
