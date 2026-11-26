import JanischLehericy.Comparison

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators
noncomputable section
namespace JanischLehericy

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ} {G : Neighborhoods ι m}
variable {X : ι → Ω → ℝ}

def localSum (G : Neighborhoods ι m) (X : ι → Ω → ℝ) (i : ι) (ω : Ω) :=
  ∑ k ∈ G.near i, X k ω

omit [MeasurableSpace Ω] in
theorem outside_self (i : ι) (ω : Ω) :
    outsideSum G X i i ω = total X ω - localSum G X i ω := by
  unfold outsideSum outside total localSum
  rw [Finset.union_self, eq_sub_iff_add_eq, sum_sdiff (Finset.subset_univ _)]

/-- Secant slope, extended by the derivative when the displacement is zero. -/
def secant (f d : ℝ → ℝ) (w y : ℝ) : ℝ :=
  if y = 0 then d w else (f w-f (w-y))/y

theorem mul_secant (f d : ℝ → ℝ) (w y : ℝ) : y*secant f d w y = f w-f (w-y) := by
  by_cases h : y = 0
  · simp [h]
  · simp [secant,h,mul_div_cancel₀]

theorem secant_witness {f d : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (d x) x) (w y : ℝ) :
    ∃ t : ℝ, |w-t| ≤ |y| ∧ secant f d w y = d t := by
  have hcont := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  rcases lt_trichotomy y 0 with h | rfl | h
  · obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope f d (show w < w-y by linarith)
      hcont.continuousOn (fun x _ => hf x)
    refine ⟨t, ?_, ?_⟩
    · rw [abs_of_nonpos (by linarith [ht.1] : w-t ≤ 0), abs_of_neg h]
      linarith [ht.2]
    · rw [secant, if_neg h.ne, he]
      field_simp
      ring
  · exact ⟨w,by simp,by simp [secant]⟩
  · obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope f d (show w-y < w by linarith)
      hcont.continuousOn (fun x _ => hf x)
    refine ⟨t, ?_, ?_⟩
    · rw [abs_of_nonneg (by linarith [ht.2] : 0 ≤ w-t), abs_of_pos h]
      linarith [ht.1]
    · simpa [secant, h.ne'] using he.symm

omit [IsProbabilityMeasure μ] [DecidableEq ι] in
theorem integral_pairs (g : ι → ι → Ω → ℝ) (hg : ∀ i j, Integrable (g i j) μ) :
    (∫ ω, pairs G (fun i j => g i j ω) ∂μ) = pairs G (fun i j => ∫ ω, g i j ω ∂μ) := by
  simp [pairs, integral_finset_sum univ (fun i _ => integrable_finset_sum (G.near i) (fun j _ => hg i j)),
    integral_finset_sum _ (fun j _ => hg _ j)]

omit [IsProbabilityMeasure μ] [DecidableEq ι] in
theorem integrable_pairs (g : ι → ι → Ω → ℝ) (hg : ∀ i j, Integrable (g i j) μ) :
    Integrable (fun ω => pairs G (fun i j => g i j ω)) μ :=
  integrable_finset_sum univ (fun i _ => integrable_finset_sum (G.near i) (fun j _ => hg i j))

omit [IsProbabilityMeasure μ] in
theorem abs_pair_covariance (H : NormalizedFamily G μ X) (i j : ι) (ω : Ω) :
    |∫ t, X i t * X j t ∂μ| ≤ envelope μ (X i) ω * envelope μ (X j) ω := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := X i) (g := X j)
    (p := 2) (q := 2) (by exact Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩)
    (by simpa using H.squareIntegrable i) (by simpa using H.squareIntegrable j)
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at h
  have h' := norm_integral_le_integral_norm (μ := μ) (fun t => X i t*X j t)
  simp only [Real.norm_eq_abs, abs_mul] at h'
  exact (h'.trans h).trans (mul_le_mul (le_max_right _ _) (le_max_right _ _)
    (Real.sqrt_nonneg _) (envelope_nonneg _ _))

omit [IsProbabilityMeasure μ] in
/-- The graph identity common to the variance calculation and to the Stein
test. The singleton is independent of the sum outside its own neighborhood. -/
theorem row_identity (H : NormalizedFamily G μ X) (f : ℝ → ℝ) (hf : Measurable f)
    (s : ι → Ω → ℝ)
    (hs : ∀ i ω, localSum G X i ω * s i ω = f (total X ω)-f (outsideSum G X i i ω))
    (hF : ∀ i, MemLp (fun ω => f (outsideSum G X i i ω)) 2 μ)
    (hT : ∀ i j, Integrable (fun ω => X i ω*X j ω*s i ω) μ) :
    (∫ ω, total X ω*f (total X ω) ∂μ) = pairs G (fun i j => ∫ ω, X i ω*X j ω*s i ω ∂μ) := by
  let T := fun i j ω => X i ω*X j ω*s i ω
  let O := fun i ω => X i ω*f (outsideSum G X i i ω)
  have hO i : Integrable (O i) μ := (H.squareIntegrable i).integrable_mul (hF i)
  have ho i : (∫ ω, O i ω ∂μ) = 0 := by
    have hV : Measurable (outsideSum G X i i) := Finset.measurable_sum _ (fun k _ => H.measurable k)
    have h := (pair_independent_outside G H.dependency i i).integral_fun_comp_mul_comp
      ((H.measurable i).prodMk (H.measurable i)).aemeasurable hV.aemeasurable
      (f := Prod.fst) measurable_fst.aestronglyMeasurable hf.aestronglyMeasurable
    change (∫ ω, O i ω ∂μ) = (∫ ω, X i ω ∂μ) * _ at h
    simpa [H.centered] using h
  have he ω : total X ω*f (total X ω) = (∑ i, O i ω) + pairs G (fun i j => T i j ω) := by
    simp only [total, Finset.sum_mul, pairs, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    have h : ∑ j ∈ G.near i, T i j ω = X i ω * (localSum G X i ω*s i ω) := by
      simp only [T,localSum,Finset.sum_mul,mul_sum,mul_assoc]
    rw [h, hs]
    dsimp only [O,total]
    ring
  simp_rw [he]
  rw [integral_add (integrable_finset_sum _ (fun i _ => hO i)) (integrable_pairs _ hT),
    integral_finset_sum _ (fun i _ => hO i), integral_pairs _ hT]
  simp [ho]

theorem sum_pair_covariance (H : NormalizedFamily G μ X) :
    pairs G (fun i j => ∫ ω, X i ω*X j ω ∂μ) = 1 := by
  have h := row_identity H id measurable_id (fun _ _ => 1)
    (fun i ω => by rw [outside_self]; simp)
    (fun i => memLp_finset_sum _ (fun k _ => H.squareIntegrable k))
    (fun i j => by simpa using (H.squareIntegrable i).integrable_mul (H.squareIntegrable j))
  simp only [id_eq, mul_one, ← sq] at h
  rw [← h, total_second_moment H]

omit [IsProbabilityMeasure μ] in
theorem outside_covariance (H : NormalizedFamily G μ X) (i j : ι) (d : ℝ → ℝ) (hd : Measurable d) :
    (∫ ω, X i ω*X j ω*d (outsideSum G X i j ω) ∂μ) =
      (∫ ω, X i ω*X j ω ∂μ) * ∫ ω, d (outsideSum G X i j ω) ∂μ :=
  (pair_independent_outside G H.dependency i j).integral_fun_comp_mul_comp
    ((H.measurable i).prodMk (H.measurable j)).aemeasurable
    (Finset.measurable_sum _ (fun k _ => H.measurable k)).aemeasurable
    (measurable_fst.mul measurable_snd).aestronglyMeasurable hd.aestronglyMeasurable

end JanischLehericy
