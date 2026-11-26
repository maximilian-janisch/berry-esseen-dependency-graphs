import JanischLehericy.NormalTest
import JanischLehericy.Induction

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators
noncomputable section
namespace JanischLehericy

def normalResidual (α z x : ℝ) := smoothedSlope z α x - x*average α (solution z) x

theorem normalResidual_eq {α : ℝ} (hα : 0 < α) (z x : ℝ) :
    normalResidual α z x = (∫ t in x..x+α, slopeAt z t-x*solution z t)/α := by
  unfold normalResidual
  rw [smoothedSlope_eq hα]
  unfold average
  rw [intervalIntegral.integral_sub (slope_integrable z _ _)
    (((continuous_solution z).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul]
  ring

theorem normalResidual_upper {α : ℝ} (hα : 0 < α) (z x : ℝ) :
    normalResidual α z x ≤ (if x ≤ z then 1 else 0) - normalCDF z + 2*α := by
  rw [normalResidual_eq hα,div_le_iff₀ hα]
  have h := intervalIntegral.integral_mono_on (by linarith : x ≤ x+α)
    ((slope_integrable z x (x+α)).sub (((continuous_solution z).intervalIntegrable _ _).const_mul x))
    (g := fun _ => (if x ≤ z then 1 else 0)-normalCDF z+2*α) intervalIntegrable_const (fun t ht => by
      have hp := mul_le_mul (show t-x ≤ α by linarith [ht.2]) (solution_le_two z t)
        (solution_nonneg z t) hα.le
      change drift z t - jump z t + (1-normalCDF z) - x * solution z t ≤ _
      rw [drift,jump_apply]
      split_ifs <;> nlinarith [ht.1])
  simpa only [intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,mul_comm α] using h

theorem normalResidual_lower {α : ℝ} (hα : 0 < α) (z x : ℝ) :
    (if x ≤ z then 1 else 0)-normalCDF (z+α) ≤ normalResidual α (z+α) x := by
  rw [normalResidual_eq hα,le_div_iff₀ hα]
  have h := intervalIntegral.integral_mono_on_of_le_Ioo (by linarith : x ≤ x+α)
    (f := fun _ => (if x ≤ z then 1 else 0)-normalCDF (z+α)) intervalIntegrable_const
    ((slope_integrable (z+α) x (x+α)).sub (((continuous_solution (z+α)).intervalIntegrable _ _).const_mul x))
    (fun t ht => by
      have hp := mul_nonneg (show 0 ≤ t-x by linarith [ht.1]) (solution_nonneg (z+α) t)
      change _ ≤ drift (z+α) t - jump (z+α) t + (1-normalCDF (z+α)) - x*solution (z+α) t
      rw [drift,jump_apply]
      split_ifs <;> nlinarith [ht.2])
  simpa only [intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,mul_comm α] using h

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ}
variable {G : Neighborhoods ι m} {X : ι → Ω → ℝ}

/-- The Stein smoothing lemma with the constants used in the induction. -/
theorem stein_estimate (H : NormalizedFamily G μ X) : SteinEstimate G μ X := by
  intro α hα _ K hK z
  let W := total X
  let I := (W ⁻¹' Iic z).indicator (fun _ => (1:ℝ))
  have hW : Measurable W := Finset.measurable_sum _ (fun i _ => H.measurable i)
  have hWi : Integrable W μ := (memLp_finset_sum univ (fun i _ => H.squareIntegrable i)).integrable (by norm_num)
  have hI : Integrable I μ := (integrable_const (1:ℝ)).indicator (hW measurableSet_Iic)
  have hprob : (∫ ω, I ω ∂μ) = μ.real (W ⁻¹' Iic z) := integral_indicator_one (hW measurableSet_Iic)
  have hres (q : ℝ) : Integrable (fun ω => normalResidual α q (W ω)) μ ∧
      |∫ ω, normalResidual α q (W ω) ∂μ| ≤ 6*K := by
    let T := normalTest hα q
    obtain ⟨B,hB⟩ := T.dBound
    obtain ⟨D,hD⟩ := T.fBound
    have hf := (continuous_iff_continuousAt.mpr fun x => (T.deriv x).continuousAt).measurable
    have hd : Integrable (fun ω => T.d (W ω)) μ := (MemLp.of_bound (p := 1)
      (T.measurable.comp hW).aestronglyMeasurable B (Filter.Eventually.of_forall fun ω => hB _)).integrable le_rfl
    have hg : Integrable (fun ω => W ω*T.f (W ω)) μ := by
      simpa only [Function.comp_apply,mul_comm] using hWi.bdd_mul (hf.comp hW).aestronglyMeasurable ⟨D,fun ω => hD _⟩
    refine ⟨hd.sub hg, ?_⟩
    change |∫ ω, T.d (W ω)-W ω*T.f (W ω) ∂μ| ≤ _
    rw [integral_sub hd hg]
    exact stein_residual H hα T hK
  have hup := integral_mono (hres z).1 ((hI.sub (integrable_const (normalCDF z))).add (integrable_const (2*α)))
    (fun ω => normalResidual_upper hα z (W ω))
  have hlo := integral_mono (hI.sub (integrable_const (normalCDF (z+α)))) (hres (z+α)).1
    (fun ω => normalResidual_lower hα z (W ω))
  change (∫ ω, normalResidual α z (W ω) ∂μ) ≤ ∫ ω, I ω-normalCDF z+2*α ∂μ at hup
  change (∫ ω, I ω-normalCDF (z+α) ∂μ) ≤ _ at hlo
  have hsub q : Integrable (fun ω => I ω-normalCDF q) μ := hI.sub (integrable_const _)
  rw [integral_add (hsub z) (integrable_const _), integral_sub hI (integrable_const _),hprob] at hup
  rw [integral_sub hI (integrable_const _),hprob] at hlo
  simp only [integral_const,measureReal_univ_eq_one,one_smul] at hup hlo
  have h1 := (abs_le.mp (hres z).2).1
  have h2 := (abs_le.mp (hres (z+α)).2).2
  have hn := normalCDF_increment (show z ≤ z+α by linarith)
  change |μ.real (W ⁻¹' Iic z)-normalCDF z| ≤ _
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- For a centered, variance-one sum with a dependency graph, the Kolmogorov
distance to the standard normal is at most the truncated-moment bound. -/
theorem truncated_bound (G : Neighborhoods ι m) (X : ι → Ω → ℝ) : TruncatedBound G μ X :=
  truncated_of_stein (fun _ _ _ H => stein_estimate H) G X

/-- Janisch–Lehéricy's normalized bound, simultaneously for every 2 < δ ≤ 3. -/
theorem janisch_lehericy (G : Neighborhoods ι m) (X : ι → Ω → ℝ) : JanischLehericyBound G μ X :=
  conjecture_of_truncated (truncated_bound G X)

end JanischLehericy
