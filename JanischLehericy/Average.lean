import JanischLehericy.SteinResidual

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
noncomputable section
namespace JanischLehericy

def average (α : ℝ) (f : ℝ → ℝ) (x : ℝ) := (∫ t in x..x+α, f t)/α

theorem interval_sandwich {f : ℝ → ℝ} {a b l r : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (h : ∀ t ∈ Icc a b, l ≤ f t ∧ f t ≤ r) :
    (b-a)*l ≤ (∫ t in a..b, f t) ∧ (∫ t in a..b, f t) ≤ (b-a)*r := by
  constructor
  · simpa only [intervalIntegral.integral_const, smul_eq_mul] using
      intervalIntegral.integral_mono_on hab (intervalIntegrable_const) hf (fun t ht => (h t ht).1)
  · simpa only [intervalIntegral.integral_const, smul_eq_mul] using
      intervalIntegral.integral_mono_on hab hf (intervalIntegrable_const) (fun t ht => (h t ht).2)

theorem average_bounds {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ} {x l r : ℝ}
    (hf : IntervalIntegrable f volume x (x+α)) (h : ∀ t ∈ Icc x (x+α), l ≤ f t ∧ f t ≤ r) :
    l ≤ average α f x ∧ average α f x ≤ r := by
  have ⟨h1,h2⟩ := interval_sandwich (by linarith) hf h
  unfold average
  exact ⟨(le_div_iff₀ hα).mpr (by linarith), (div_le_iff₀ hα).mpr (by linarith)⟩

theorem average_zero_based (α : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    average α f x = (∫ t in 0..α, f (t+x))/α := by
  rw [intervalIntegral.integral_comp_add_right]
  simp [average,add_comm]

theorem average_monotone {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ} (hf : Monotone f) :
    Monotone (average α f) := by
  intro x y h
  rw [average_zero_based,average_zero_based]
  apply div_le_div_of_nonneg_right _ hα.le
  apply intervalIntegral.integral_mono hα.le
      ((hf.comp (monotone_id.add_const x)).intervalIntegrable)
      ((hf.comp (monotone_id.add_const y)).intervalIntegrable)
  intro t
  exact hf (by dsimp; linarith)

theorem average_increment {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ} (hf : Monotone f)
    {x y : ℝ} (hxy : y ≤ x) :
    average α f x-average α f y ≤ min 1 ((x-y)/α) * (f (x+α)-f y) := by
  have h0 : 0 ≤ f (x+α)-f y := sub_nonneg.mpr (hf (by linarith))
  have hbox a b (ha : y ≤ a) (hb : b ≤ x+α) (hab : a ≤ b) :=
    interval_sandwich hab hf.intervalIntegrable (fun t (ht : t ∈ Icc a b) =>
      And.intro (hf (ha.trans ht.1)) (hf (ht.2.trans hb)))
  have hx := hbox x (x+α) hxy le_rfl (by linarith)
  have hy := hbox y (y+α) le_rfl (by linarith) (by linarith)
  have hd := intervalIntegral.integral_interval_sub_interval_comm' (f := f)
    (μ := volume) (a := x) (b := x+α) (c := y) (d := y+α)
    hf.intervalIntegrable hf.intervalIntegrable hf.intervalIntegrable
  have hx' := hbox (y+α) (x+α) (by linarith) le_rfl (by linarith)
  have hy' := hbox y x le_rfl (by linarith) hxy
  unfold average
  rw [← sub_div]
  rcases le_total 1 ((x-y)/α) with h | h
  · rw [min_eq_left h,one_mul,div_le_iff₀ hα]
    linarith only [hx.2,hy.1]
  · rw [min_eq_right h,div_mul_eq_mul_div,div_le_div_iff_of_pos_right hα,hd]
    linarith only [hx'.2,hy'.1]

theorem average_hasDerivAt {α : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (average α f) ((f (x+α)-f x)/α) x := by
  let F := fun b => ∫ t in (0:ℝ)..b, f t
  have hF y : HasDerivAt F (f y) y := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable _ _) hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have he : average α f = fun y => (F (y+α)-F y)/α := by
    funext y
    rw [average, ← intervalIntegral.integral_interval_sub_left (a := 0)
      (hf.intervalIntegrable 0 (y+α)) (hf.intervalIntegrable 0 y)]
  rw [he]
  simpa only [Function.comp_def, id_eq, mul_one] using
    (((hF (x+α)).comp x ((hasDerivAt_id x).add_const α)).sub (hF x)).div_const α

theorem integral_ramp (ν : Measure ℝ) (α w s : ℝ) :
    (∫ u, rampBound α w u s ∂ν) = ν.real {u | |w-u| ≤ α+s} * min 1 (s/α) := by
  have h : MeasurableSet {u : ℝ | |w-u| ≤ α+s} := measurableSet_le (by fun_prop) measurable_const
  change (∫ u, ({u : ℝ | |w-u| ≤ α+s} : Set ℝ).indicator (fun _ => min 1 (s/α)) u ∂ν) = _
  rw [integral_indicator h, setIntegral_const, smul_eq_mul]

/-- Averaging two monotone functions turns a bound on their combined
Stieltjes measure into the spatially localized increment used by the graph. -/
theorem average_oscillation {α : ℝ} (hα : 0 < α) {g j : ℝ → ℝ}
    (hg : Monotone g) (hj : Monotone j) (F : StieltjesFunction) [IsFiniteMeasure F.measure]
    (hF : ∀ x, F x = g x+j x) (w t s : ℝ) (hs : |w-t| ≤ s) :
    |(average α g w - average α j w) - (average α g t - average α j t)| ≤
      ∫ u, rampBound α w u s ∂F.measure := by
  let x := max w t
  let y := min w t
  have hxy : y ≤ x := (min_le_left _ _).trans (le_max_left _ _)
  have hl : x-y = |w-t| := by
    dsimp [x,y]
    rcases le_total w t with h | h <;> simp [h,abs_of_nonpos,abs_of_nonneg,sub_nonneg]
  have hin : Ioc y (x+α) ⊆ {u | |w-u| ≤ α+s} := by
    intro u hu
    change |w-u| ≤ α+s
    obtain ⟨h1,h2⟩ := hu
    have h3 : y ≤ w := min_le_left _ _
    have h4 : w ≤ x := le_max_left _ _
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hm := measureReal_mono (μ := F.measure) hin
  have h0 := F.mono (show y ≤ x+α by linarith)
  rw [measureReal_def, F.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr h0)] at hm
  have hk := min_le_min_left 1 (div_le_div_of_nonneg_right (hl.trans_le hs) hα.le)
  have hinc := add_le_add (average_increment hα hg hxy) (average_increment hα hj hxy)
  have hdiff : |(average α g w-average α j w)-(average α g t-average α j t)| ≤
      (average α g x-average α g y)+(average α j x-average α j y) := by
    have h1 := average_monotone hα hg hxy
    have h2 := average_monotone hα hj hxy
    rcases le_total w t with h | h
    · dsimp [x,y] at *
      rw [max_eq_right h,min_eq_left h] at *
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    · dsimp [x,y] at *
      rw [max_eq_left h,min_eq_right h] at *
      exact abs_le.mpr ⟨by linarith,by linarith⟩
  rw [integral_ramp,mul_comm]
  apply hdiff.trans (hinc.trans _)
  rw [← mul_add]
  have heq : g (x+α)-g y + (j (x+α)-j y) = F (x+α)-F y := by rw [hF,hF]; ring
  rw [heq]
  exact mul_le_mul hk hm (sub_nonneg.mpr h0) (le_min zero_le_one (div_nonneg ((abs_nonneg _).trans hs) hα.le))

end JanischLehericy
