import JanischLehericy.Statement

open MeasureTheory ProbabilityTheory Set
noncomputable section
namespace JanischLehericy

theorem normal_density_le_half (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1/2 := by
  have hs : 2 ≤ Real.sqrt (2*Real.pi) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith [Real.pi_gt_three])
  have h := Real.exp_le_one_iff.mpr (show -(x^2)/2 ≤ 0 by nlinarith [sq_nonneg x])
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  calc
    _ ≤ (Real.sqrt (2*Real.pi))⁻¹ * 1 := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ _ := by rw [mul_one, inv_eq_one_div]; gcongr

theorem normalCDF_increment {a b : ℝ} (hab : a ≤ b) :
    normalCDF b - normalCDF a ≤ (b-a)/2 := by
  let γ := gaussianReal 0 1
  have he : Iic b \ Iic a = Ioc a b := by ext x; simp
  have hd := measureReal_diff (μ := γ) (Iic_subset_Iic.mpr hab) measurableSet_Iic
  rw [he] at hd
  change cdf γ b - cdf γ a ≤ _
  rw [cdf_eq_real, cdf_eq_real, ← hd]
  unfold Measure.real
  rw [gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal
    (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  haveI : IsFiniteMeasure (volume.restrict (Ioc a b)) := by
    constructor
    simp [Real.volume_Ioc]
  calc
    _ ≤ ∫ _ in Ioc a b, (1/2:ℝ) := integral_mono (integrable_gaussianPDFReal _ _).restrict
      (integrable_const _) normal_density_le_half
    _ = _ := by simp [Real.volume_real_Ioc_of_le hab]; ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Closed intervals, including atoms at the left endpoint. The scaling is the
reciprocal of the deleted sum's standard deviation. -/
theorem interval_of_cdf {W : Ω → ℝ} (hW : Measurable W) {c η : ℝ} (hc : 0 < c)
    (hc2 : c ≤ 2) (hη : 0 ≤ η) (H : CDFBound μ (fun ω => c*W ω) η)
    (u h : ℝ) (hh : 0 ≤ h) :
    μ.real {ω | |W ω-u| ≤ h} ≤ min 1 (2*h) + 2*η := by
  let Y := fun ω => c*W ω
  have hY : Measurable Y := hW.const_mul c
  have hp := prob_le_one (μ := μ) {ω | |W ω-u| ≤ h}
  have hlen : μ.real {ω | |W ω-u| ≤ h} ≤ 2*h + 2*η := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let a := c*(u-h)-ε
    let b := c*(u+h)
    have hab : a ≤ b := by dsimp [a,b]; nlinarith only [hε, mul_nonneg hc.le hh]
    have hin : {ω | |W ω-u| ≤ h} ⊆ (Y ⁻¹' Iic b) \ (Y ⁻¹' Iic a) := by
      intro ω hω
      change |W ω-u| ≤ h at hω
      obtain ⟨hl,hu⟩ := abs_le.mp hω
      have h1 := mul_le_mul_of_nonneg_left (show u-h ≤ W ω by linarith) hc.le
      have h2 := mul_le_mul_of_nonneg_left (show W ω ≤ u+h by linarith) hc.le
      exact ⟨h2, fun h' => by change c*W ω ≤ c*(u-h)-ε at h'; linarith⟩
    have hs := measureReal_mono (μ := μ) hin
    rw [measureReal_diff (preimage_mono (Iic_subset_Iic.mpr hab)) (hY measurableSet_Iic)] at hs
    have hf := normalCDF_increment hab
    have h1 := (abs_le.mp (H a)).1
    have h2 := (abs_le.mp (H b)).2
    change -η ≤ μ.real (Y ⁻¹' Iic a) - normalCDF a at h1
    change μ.real (Y ⁻¹' Iic b) - normalCDF b ≤ η at h2
    have hd : b-a = 2*c*h+ε := by dsimp [a,b]; ring
    rw [hd] at hf
    nlinarith only [hs,hf,h1,h2,hε,mul_le_mul_of_nonneg_right hc2 hh]
  rw [← min_add_add_right]
  exact le_min (by linarith) hlen

/-- Scalar interval estimate after the independent pair has been fixed. -/
theorem ramp_interval_product {α L η : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hL : 0 ≤ L) (hη : 0 ≤ η) :
    min 1 (4*L/α) * (min 1 (2*(α+10*L)) + η)
      ≤ (28 + 4*η/α) * min 1 L := by
  let b := min 1 (4*L/α)
  have hb0 : 0 ≤ b := le_min zero_le_one (div_nonneg (by linarith) hα.le)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hb : b*α ≤ 4*L := (le_div_iff₀ hα).mp (min_le_right _ _)
  have hprod : b * min 1 (2*(α+10*L)) ≤ 28*min 1 L := by
    rcases le_total L 1 with h | h
    · rw [min_eq_right h]
      have hp := mul_le_mul_of_nonneg_left (min_le_right 1 (2*(α+10*L))) hb0
      nlinarith only [hp, hb, mul_le_mul_of_nonneg_right hb1 hL]
    · rw [min_eq_left h, mul_one]
      have hp := mul_le_mul_of_nonneg_left (min_le_left 1 (2*(α+10*L))) hb0
      nlinarith only [hp, hb1]
  have hb' : b ≤ 4*min 1 L/α := by
    apply (le_div_iff₀ hα).mpr
    rcases le_total L 1 with h | h
    · simpa [min_eq_right h] using hb
    · rw [min_eq_left h, mul_one]
      linarith [mul_le_mul_of_nonneg_right hb1 hα.le]
  have he := mul_le_mul_of_nonneg_right hb' hη
  change b * _ ≤ _
  rw [mul_add, add_mul]
  calc
    _ ≤ 28 * min 1 L + (4 * min 1 L / α) * η := add_le_add hprod he
    _ = _ := by ring

end JanischLehericy
