import JanischLehericy.Average
import JanischLehericy.Gaussian

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace JanischLehericy

def solution (z x : ℝ) : ℝ :=
  normalCDF (min x z) * (1-normalCDF (max x z)) / density x

def drift (z x : ℝ) := x*solution z x
def jump (z : ℝ) := cdf (Measure.dirac z)

theorem jump_apply (z x : ℝ) : jump z x = if z ≤ x then 1 else 0 := by
  simp only [jump,cdf_eq_real,measureReal_def,Measure.dirac_apply' _ measurableSet_Iic,
    Set.indicator_apply,Set.mem_Iic,Pi.one_apply]
  split_ifs <;> simp

theorem solution_left {x z : ℝ} (h : x ≤ z) :
    solution z x = (1-normalCDF z)*mills (-x) := by
  simp [solution,mills,min_eq_left h,max_eq_right h,normalCDF_neg,density_neg]
  ring

theorem solution_right {x z : ℝ} (h : z ≤ x) : solution z x = normalCDF z*mills x := by
  simp only [solution,mills,min_eq_right h,max_eq_left h]
  ring

theorem solution_nonneg (z x : ℝ) : 0 ≤ solution z x :=
  div_nonneg (mul_nonneg (cdf_nonneg _ _) (sub_nonneg.mpr (cdf_le_one _ _))) (density_pos _).le

theorem solution_le_two (z x : ℝ) : solution z x ≤ 2 := by
  have hm : mills 0 ≤ 2 := by
    have h0 := normalCDF_neg 0
    rw [neg_zero] at h0
    have hc : 1-normalCDF 0 = 1/2 := by linarith
    unfold mills
    rw [hc,div_eq_mul_inv]
    linarith [density_zero_inv_le_three]
  rcases le_total x 0 with hx | hx
  · apply le_trans _ ((mills_antitone (by linarith : 0 ≤ -x)).trans hm)
    rw [mills, normalCDF_neg, density_neg, sub_sub_cancel, solution]
    apply div_le_div_of_nonneg_right _ (density_pos _).le
    apply le_trans (mul_le_of_le_one_right (cdf_nonneg _ _) (by linarith [show 0 ≤ normalCDF (max x z) from cdf_nonneg _ _]))
    exact monotone_cdf _ (min_le_left _ _)
  · apply le_trans _ ((mills_antitone hx).trans hm)
    unfold solution mills
    apply div_le_div_of_nonneg_right _ (density_pos _).le
    apply le_trans (mul_le_of_le_one_left (sub_nonneg.mpr (cdf_le_one _ _)) (cdf_le_one _ _))
    exact sub_le_sub_left (monotone_cdf _ (le_max_left _ _)) _

theorem continuous_solution (z : ℝ) : Continuous (solution z) := by
  have hF := continuous_iff_continuousAt.mpr fun x => (normalCDF_deriv x).continuousAt
  have hp := continuous_iff_continuousAt.mpr fun x => (density_deriv x).continuousAt
  exact ((hF.comp (continuous_id.min continuous_const)).mul
    (continuous_const.sub (hF.comp (continuous_id.max continuous_const)))).div hp (fun x => (density_pos x).ne')

theorem monotone_drift (z : ℝ) : Monotone (drift z) := by
  have hl {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ z) : drift z x ≤ drift z y := by
    have h := mul_le_mul_of_nonneg_left (monotone_x_mills (neg_le_neg hxy))
      (sub_nonneg.mpr (show normalCDF z ≤ 1 from cdf_le_one _ _))
    dsimp only [drift]
    rw [solution_left (hxy.trans hy),solution_left hy]
    linarith only [h]
  have hr {x y : ℝ} (hxy : x ≤ y) (hx : z ≤ x) : drift z x ≤ drift z y := by
    have h := mul_le_mul_of_nonneg_left (monotone_x_mills hxy) (show 0 ≤ normalCDF z from cdf_nonneg _ _)
    dsimp only [drift]
    rw [solution_right hx,solution_right (hx.trans hxy)]
    linarith only [h]
  intro x y hxy
  rcases le_total y z with hy | hy
  · exact hl hxy hy
  rcases le_total z x with hx | hx
  · exact hr hxy hx
  · exact (hl hx le_rfl).trans (hr hy le_rfl)

theorem drift_bounds (z x : ℝ) : normalCDF z-1 ≤ drift z x ∧ drift z x ≤ normalCDF z := by
  constructor
  · apply le_trans _ (monotone_drift z (min_le_left x z))
    unfold drift
    rw [solution_left (min_le_right x z)]
    have h := mul_le_mul_of_nonneg_left (mills_upper (-min x z)) (sub_nonneg.mpr (show normalCDF z ≤ 1 from cdf_le_one _ _))
    linarith only [h]
  · apply le_trans (monotone_drift z (le_max_left x z)) _
    unfold drift
    rw [solution_right (le_max_right x z)]
    have h := mul_le_mul_of_nonneg_left (mills_upper (max x z)) (show 0 ≤ normalCDF z from cdf_nonneg _ _)
    linarith only [h]

def slopeAt (z x : ℝ) := drift z x - jump z x + (1-normalCDF z)

theorem solution_deriv_left {x z : ℝ} (hx : x < z) :
    HasDerivAt (solution z) (slopeAt z x) x := by
  have h := ((mills_deriv (-x)).comp x (hasDerivAt_id x).neg).const_mul (1-normalCDF z)
  have he : solution z =ᶠ[𝓝 x] (fun t => (1-normalCDF z)*mills (-t)) := by
    filter_upwards [gt_mem_nhds hx] with t ht using solution_left ht.le
  apply (h.congr_of_eventuallyEq he).congr_deriv
  simp only [slopeAt,drift,solution_left hx.le,jump_apply,if_neg (not_le.mpr hx)]
  ring

theorem solution_deriv_right {x z : ℝ} (hx : z < x) :
    HasDerivAt (solution z) (slopeAt z x) x := by
  have h := (mills_deriv x).const_mul (normalCDF z)
  have he : solution z =ᶠ[𝓝 x] (fun t => normalCDF z*mills t) := by
    filter_upwards [lt_mem_nhds hx] with t ht using solution_right ht.le
  apply (h.congr_of_eventuallyEq he).congr_deriv
  simp only [slopeAt,drift,solution_right hx.le,jump_apply,if_pos hx.le]
  ring

theorem slope_integrable (z a b : ℝ) : IntervalIntegrable (slopeAt z) volume a b :=
  ((monotone_drift z).intervalIntegrable.sub (jump z).mono.intervalIntegrable).add intervalIntegrable_const

theorem integral_slope {a b : ℝ} (hab : a ≤ b) (z : ℝ) :
    (∫ t in a..b, slopeAt z t) = solution z b-solution z a := by
  have hl {v w : ℝ} (h : v ≤ w) (hw : w ≤ z) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h (f := solution z) (continuous_solution z).continuousOn
      (fun t (ht : t ∈ Ioo v w) => solution_deriv_left (ht.2.trans_le hw)) (slope_integrable z v w)
  have hr {v w : ℝ} (h : v ≤ w) (hv : z ≤ v) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h (f := solution z) (continuous_solution z).continuousOn
      (fun t (ht : t ∈ Ioo v w) => solution_deriv_right (hv.trans_lt ht.1)) (slope_integrable z v w)
  rcases le_total b z with h | h
  · exact hl hab h
  rcases le_total z a with h' | h'
  · exact hr hab h'
  rw [← intervalIntegral.integral_add_adjacent_intervals (slope_integrable z a z) (slope_integrable z z b),
    hl h' le_rfl,hr h le_rfl]
  ring

def variationFunction (z : ℝ) : StieltjesFunction :=
  {toFun := drift z, mono' := monotone_drift z,
   right_continuous' := fun _ => (continuous_id.mul (continuous_solution z)).continuousAt.continuousWithinAt} + jump z

theorem variation_apply (z x : ℝ) : variationFunction z x = drift z x+jump z x := rfl

theorem variation_mass (z : ℝ) : (variationFunction z).measure Set.univ ≤ 2 := by
  let F := variationFunction z
  have hbounds x : normalCDF z-1 ≤ F x ∧ F x ≤ normalCDF z+1 := by
    rw [show F x = drift z x+jump z x from rfl]
    exact ⟨by linarith [(drift_bounds z x).1,show 0 ≤ jump z x from cdf_nonneg _ _],
      by linarith [(drift_bounds z x).2,show jump z x ≤ 1 from cdf_le_one _ _]⟩
  have hl : BddBelow (range F) := ⟨_,forall_mem_range.mpr (fun x => (hbounds x).1)⟩
  have hu : BddAbove (range F) := ⟨_,forall_mem_range.mpr (fun x => (hbounds x).2)⟩
  change F.measure Set.univ ≤ 2
  rw [F.measure_univ (tendsto_atBot_ciInf F.mono hl) (tendsto_atTop_ciSup F.mono hu)]
  have hsup := ciSup_le (fun x => (hbounds x).2)
  have hinf := le_ciInf (fun x => (hbounds x).1)
  exact_mod_cast (ENNReal.ofReal_le_ofReal (show (⨆ x, F x)-(⨅ x, F x) ≤ 2 by linarith))

def smoothedSlope (z α x : ℝ) := average α (drift z) x - average α (jump z) x + (1-normalCDF z)

theorem smoothedSlope_eq {α : ℝ} (hα : 0 < α) (z x : ℝ) :
    smoothedSlope z α x = average α (slopeAt z) x := by
  simp only [smoothedSlope, average, slopeAt]
  rw [intervalIntegral.integral_add ((monotone_drift z).intervalIntegrable.sub (jump z).mono.intervalIntegrable)
    intervalIntegrable_const, intervalIntegral.integral_sub (monotone_drift z).intervalIntegrable (jump z).mono.intervalIntegrable,
    intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

def normalTest {α : ℝ} (hα : 0 < α) (z : ℝ) : SmoothTest α := by
  let F := variationFunction z
  letI : IsFiniteMeasure F.measure := ⟨(variation_mass z).trans_lt (by norm_num)⟩
  refine ⟨average α (solution z), smoothedSlope z α, F.measure, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (F.measure Set.univ).toReal ≤ 2
    exact (ENNReal.toReal_mono (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (variation_mass z)).trans_eq (by norm_num)
  · refine ⟨2,fun x => abs_le.mpr ?_⟩
    exact average_bounds hα ((continuous_solution z).intervalIntegrable _ _) (fun t _ =>
      ⟨by linarith [solution_nonneg z t],solution_le_two z t⟩)
  · refine ⟨3,fun x => abs_le.mpr ?_⟩
    rw [smoothedSlope_eq hα]
    apply average_bounds hα (slope_integrable _ _ _)
    intro t _
    unfold slopeAt
    have hg := drift_bounds z t
    have hs : 0 ≤ jump z t := cdf_nonneg _ _
    have hs' : jump z t ≤ 1 := cdf_le_one _ _
    constructor <;> linarith
  · intro x
    rw [smoothedSlope_eq hα,average,integral_slope (by linarith : x ≤ x+α)]
    exact average_hasDerivAt (continuous_solution z) x
  · exact (((average_monotone hα (monotone_drift z)).measurable.sub
      (average_monotone hα (jump z).mono).measurable).add_const _)
  · intro w t s hs
    simpa only [smoothedSlope,add_sub_add_right_eq_sub] using
      average_oscillation hα (monotone_drift z) (jump z).mono F (variation_apply z) w t s hs

end JanischLehericy
