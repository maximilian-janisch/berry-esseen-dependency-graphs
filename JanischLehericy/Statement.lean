import JanischLehericy.Budget
import JanischLehericy.Dependence
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators
noncomputable section
namespace JanischLehericy

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {m : ℕ} {X : ι → Ω → ℝ}

def total (X : ι → Ω → ℝ) (ω : Ω) : ℝ := ∑ i, X i ω

def normalCDF (z : ℝ) : ℝ := cdf (gaussianReal 0 1) z

/-- A pointwise-in-threshold formulation of a uniform Kolmogorov bound. -/
def CDFBound (μ : Measure Ω) (W : Ω → ℝ) (e : ℝ) : Prop :=
  ∀ z : ℝ, |μ.real (W ⁻¹' Iic z) - normalCDF z| ≤ e

theorem prob_le_one (s : Set Ω) : μ.real s ≤ 1 := by
  simpa using (measureReal_mono (μ := μ) (subset_univ s))

theorem cdfBound_one (W : Ω → ℝ) : CDFBound μ W 1 := by
  intro z
  have hp : 0 ≤ μ.real (W ⁻¹' Iic z) := measureReal_nonneg
  have hn : 0 ≤ normalCDF z := cdf_nonneg _ _
  have hn' : normalCDF z ≤ 1 := cdf_le_one _ _
  have hp' := prob_le_one (μ := μ) (W ⁻¹' Iic z)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [IsProbabilityMeasure μ] in
theorem CDFBound.mono {W : Ω → ℝ} {a b : ℝ} (h : CDFBound μ W a) (hab : a ≤ b) :
    CDFBound μ W b := fun z => (h z).trans hab

/-- The assumptions shared by the theorem and its induced subproblems. -/
structure NormalizedFamily [DecidableEq ι] (G : Neighborhoods ι m) (μ : Measure Ω)
    (X : ι → Ω → ℝ) : Prop where
  measurable : ∀ i, Measurable (X i)
  squareIntegrable : ∀ i, MemLp (X i) 2 μ
  centered : ∀ i, (∫ ω, X i ω ∂μ) = 0
  unitVariance : variance (total X) μ = 1
  dependency : IsDependencyGraph G μ X

theorem total_mean_zero (hs : ∀ i, MemLp (X i) 2 μ) (hc : ∀ i, (∫ ω, X i ω ∂μ) = 0) :
    (∫ ω, total X ω ∂μ) = 0 := by
  simp [total, integral_finset_sum univ (fun i _ => (hs i).integrable (by norm_num)), hc]

theorem total_second_moment [DecidableEq ι] {G : Neighborhoods ι m}
    (H : NormalizedFamily G μ X) : (∫ ω, (total X ω)^2 ∂μ) = 1 := by
  rw [← H.unitVariance, variance_of_integral_eq_zero]
  · exact (memLp_finset_sum univ (fun i _ => H.squareIntegrable i)).aemeasurable
  · exact total_mean_zero H.squareIntegrable H.centered

/-- The truncated-moment Kolmogorov bound for a centered sum of variance one. -/
def TruncatedBound [DecidableEq ι] (G : Neighborhoods ι m) (μ : Measure Ω)
    (X : ι → Ω → ℝ) : Prop :=
  0 < m → NormalizedFamily G μ X → CDFBound μ (total X) (min 1 (250000 * beta μ m X))

/-- The normalized moment formulation of the Janisch–Lehéricy conjecture. -/
def JanischLehericyBound [DecidableEq ι] (G : Neighborhoods ι m) (μ : Measure Ω)
    (X : ι → Ω → ℝ) : Prop :=
  0 < m → NormalizedFamily G μ X → ∀ δ : ℝ, 2 < δ → δ ≤ 3 →
    (∀ i, Integrable (fun ω => |X i ω|^δ) μ) →
    CDFBound μ (total X) (min 1 (250000 * (m:ℝ)^(δ-1) * ∑ i, ∫ ω, |X i ω|^δ ∂μ))

omit [IsProbabilityMeasure μ] in
theorem conjecture_of_truncated [DecidableEq ι] {G : Neighborhoods ι m}
    (h : TruncatedBound G μ X) : JanischLehericyBound G μ X := by
  intro hm H δ h2 h3 hp
  apply (h hm H).mono
  apply min_le_min_left
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (beta_le_delta μ m hm X H.squareIntegrable h2 h3 hp) (by norm_num)

end JanischLehericy
