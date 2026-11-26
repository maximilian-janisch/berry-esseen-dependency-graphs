import JanischLehericy.Interval

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
noncomputable section
namespace JanischLehericy

def density := gaussianPDFReal 0 1

theorem density_pos (x : ℝ) : 0 < density x := gaussianPDFReal_pos _ _ _ one_ne_zero

theorem density_deriv (x : ℝ) : HasDerivAt density (-x*density x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const (2:ℝ)).exp.const_mul
    (Real.sqrt (2*Real.pi))⁻¹
  convert h using 1
  · funext y; simp [density,gaussianPDFReal]
  · simp [density,gaussianPDFReal]; ring

theorem normalCDF_integral (a b : ℝ) : normalCDF b - normalCDF a = ∫ x in a..b, density x := by
  suffices H : ∀ a b : ℝ, a ≤ b → normalCDF b-normalCDF a = ∫ x in a..b, density x by
    rcases le_total a b with h | h
    · exact H a b h
    · rw [intervalIntegral.integral_symm, ← H b a h]; ring
  intro a b h
  have hd := measureReal_diff (μ := gaussianReal 0 1) (Iic_subset_Iic.mpr h) measurableSet_Iic
  rw [show Iic b \ Iic a = Ioc a b by ext x; simp] at hd
  rw [normalCDF,normalCDF,cdf_eq_real,cdf_eq_real,← hd,intervalIntegral.integral_of_le h,measureReal_def,
    gaussianReal_apply_eq_integral _ one_ne_zero]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))

theorem normalCDF_deriv (x : ℝ) : HasDerivAt normalCDF (density x) x := by
  have he : normalCDF = fun y => normalCDF 0 + ∫ t in 0..y, density t := by
    funext y
    linarith [normalCDF_integral 0 y]
  have hc := continuous_iff_continuousAt.mpr fun y => (density_deriv y).continuousAt
  nth_rw 1 [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

theorem density_neg (x : ℝ) : density (-x) = density x := by simp [density,gaussianPDFReal]

theorem density_zero_inv_le_three : (density 0)⁻¹ ≤ 3 := by
  simp only [density,gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div, Real.exp_zero,inv_inv]
  apply Real.sqrt_le_iff.mpr
  exact ⟨by norm_num, by linarith [Real.pi_lt_four]⟩

theorem normalCDF_neg (x : ℝ) : normalCDF (-x) = 1-normalCDF x := by
  let f := fun t => normalCDF (-t) + normalCDF t
  have hf (t : ℝ) : HasDerivAt f 0 t := by
    have h := ((normalCDF_deriv (-t)).comp t (hasDerivAt_id t).neg).add (normalCDF_deriv t)
    simpa [f,Function.comp_def,density_neg] using h
  have hconst (t : ℝ) : f t = f x :=
    is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt) (fun t => (hf t).deriv) t x
  have ht : Tendsto f atTop (𝓝 1) := by
    have h := ((tendsto_cdf_atBot (gaussianReal 0 1)).comp tendsto_neg_atTop_atBot).add
      (tendsto_cdf_atTop (gaussianReal 0 1))
    simpa [f,normalCDF,Function.comp_def] using h
  have hc : Tendsto f atTop (𝓝 (f x)) := tendsto_const_nhds.congr (fun t => (hconst t).symm)
  have hx := tendsto_nhds_unique hc ht
  dsimp [f] at hx
  linarith

/-- Standard normal right-tail Mills ratio. -/
def mills (x : ℝ) : ℝ := (1-normalCDF x)/density x

theorem mills_nonneg (x : ℝ) : 0 ≤ mills x := div_nonneg (sub_nonneg.mpr (cdf_le_one _ _)) (density_pos _).le

theorem mills_deriv (x : ℝ) : HasDerivAt mills (x*mills x-1) x := by
  have h := ((normalCDF_deriv x).const_sub 1).div (density_deriv x) (density_pos x).ne'
  convert h using 1
  unfold mills
  field_simp [(density_pos x).ne']
  ring

private theorem small_correction :
    Tendsto (fun x : ℝ => density x*x/(1+x^2)) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun x : ℝ => 1/x)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    exact div_nonneg (mul_nonneg (density_pos x).le (by linarith)) (by positivity)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    apply (div_le_div_iff₀ (by positivity : 0 < 1+x^2) (by linarith : 0 < x)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right (normal_density_le_half x) (sq_nonneg x),
      show gaussianPDFReal 0 1 x = density x from rfl, sq_nonneg x]
  · simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))

theorem mills_lower (x : ℝ) : x ≤ (1+x^2)*mills x := by
  let f := fun t => (1-normalCDF t) - density t*t/(1+t^2)
  have hder (t : ℝ) : HasDerivAt f (-2*density t/(1+t^2)^2) t := by
    have h := ((normalCDF_deriv t).const_sub 1).sub
      (((density_deriv t).mul (hasDerivAt_id t)).div (((hasDerivAt_id t).pow 2).const_add 1) (by change 1+t^2 ≠ 0; positivity))
    convert h using 1
    simp only [id_eq, Pi.pow_apply, Pi.mul_apply]
    field_simp
    ring
  have hdec := antitone_of_deriv_nonpos (fun t => (hder t).differentiableAt) (fun t => by
    rw [(hder t).deriv]; exact div_nonpos_of_nonpos_of_nonneg (by linarith [density_pos t]) (sq_nonneg _))
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h := ((tendsto_cdf_atTop (gaussianReal 0 1)).const_sub 1).sub small_correction
    simpa [f,normalCDF] using h
  have h0 : 0 ≤ f x := le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨x,fun t ht => hdec ht⟩)
  unfold mills
  rw [← mul_div_assoc, le_div_iff₀ (density_pos _)]
  have hh : density x*x/(1+x^2) ≤ 1-normalCDF x := sub_nonneg.mp h0
  have hh' := (div_le_iff₀ (by positivity : 0 < 1+x^2)).mp hh
  linarith only [hh']

theorem mills_upper (x : ℝ) : x * mills x ≤ 1 := by
  by_cases hx : 0 < x
  · let f := fun t => (1-normalCDF t) - density t/t
    have hd (t : ℝ) (ht : 0 < t) : HasDerivAt f (density t/t^2) t := by
      have h := ((normalCDF_deriv t).const_sub 1).sub ((density_deriv t).div (hasDerivAt_id t) ht.ne')
      convert h using 1
      simp only [id_eq]
      field_simp
      ring
    have hm : MonotoneOn f (Ioi 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
      · rw [isOpen_Ioi.interior_eq]; intro t ht; exact (hd t ht).differentiableAt.differentiableWithinAt
      · rw [isOpen_Ioi.interior_eq]; intro t ht; rw [(hd t ht).deriv]; exact div_nonneg (density_pos t).le (sq_nonneg _)
    have ht : Tendsto (fun t : ℝ => density t/t) atTop (𝓝 0) := by
      apply squeeze_zero' (g := fun t : ℝ => 1/t)
      · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht; exact div_nonneg (density_pos t).le ht.le
      · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
        exact div_le_div_of_nonneg_right (by change gaussianPDFReal 0 1 t ≤ 1; linarith [normal_density_le_half t]) ht.le
      · simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
    have hlim : Tendsto f atTop (𝓝 0) := by
      simpa [f,normalCDF] using ((tendsto_cdf_atTop (gaussianReal 0 1)).const_sub 1).sub ht
    have h0 : f x ≤ 0 := ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨x,fun t ht => hm hx (hx.trans_le ht) ht⟩)
    have h1 := (le_div_iff₀ hx).mp (show 1-normalCDF x ≤ density x/x from sub_nonpos.mp h0)
    unfold mills
    rw [← mul_div_assoc, div_le_iff₀ (density_pos _)]
    linarith
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hx) (mills_nonneg x)).trans zero_le_one

theorem mills_antitone : Antitone mills :=
  antitone_of_deriv_nonpos (fun x => (mills_deriv x).differentiableAt)
    (fun x => by rw [(mills_deriv x).deriv]; linarith [mills_upper x])

theorem monotone_x_mills : Monotone (fun x => x*mills x) := by
  have h x := (hasDerivAt_id x).mul (mills_deriv x)
  apply monotone_of_deriv_nonneg (fun x => (h x).differentiableAt)
  intro x
  rw [(h x).deriv]
  dsimp
  nlinarith only [mills_lower x]

end JanischLehericy
