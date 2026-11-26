import JanischLehericy.Theorem

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace JanischLehericy

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

def momentSum (μ : Measure Ω) (Y : ι → Ω → ℝ) (δ : ℝ) : ℝ := ∑ i, ∫ ω, |Y i ω|^δ ∂μ

/-- The paper's renormalized standard deviation, with variance supplied as v. -/
def xi (N m A v δ : ℝ) : ℝ := (N/A)^(1/δ) * Real.sqrt (v/(N*m))

def standardized (μ : Measure Ω) (S : Ω → ℝ) (ω : Ω) :=
  (S ω-(∫ t, S t ∂μ))/Real.sqrt (variance S μ)

theorem xi_identity {N m A v δ : ℝ} (hN : 0 < N) (hm : 0 < m)
    (hA : 0 < A) (hv : 0 < v) (hδ : 0 < δ) :
    (xi N m A v δ)^(-δ) * (m/N)^((δ-2)/2) =
      m^(δ-1) * (Real.sqrt v)⁻¹^δ * A := by
  have hξ : 0 < xi N m A v δ := by unfold xi; positivity
  apply Real.log_injOn_pos
  · change 0 < (xi N m A v δ)^(-δ) * (m/N)^((δ-2)/2)
    positivity
  · change 0 < m^(δ-1) * (Real.sqrt v)⁻¹^δ * A
    positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hξ, Real.log_rpow (div_pos hm hN),
    Real.log_div hm.ne' hN.ne']
  unfold xi
  have hNM := mul_pos hN hm
  have hvNM := div_pos hv hNM
  have hNA := div_pos hN hA
  have hs := Real.sqrt_pos.mpr hv
  rw [Real.log_mul (Real.rpow_pos_of_pos hNA _).ne' (Real.sqrt_pos.mpr hvNM).ne',
    Real.log_rpow hNA, Real.log_div hN.ne' hA.ne', Real.log_sqrt hvNM.le,
    Real.log_div hv.ne' hNM.ne',Real.log_mul hN.ne' hm.ne',
    Real.log_mul (mul_pos (Real.rpow_pos_of_pos hm _) (Real.rpow_pos_of_pos (inv_pos.mpr hs) _)).ne' hA.ne',
    Real.log_mul (Real.rpow_pos_of_pos hm _).ne' (Real.rpow_pos_of_pos (inv_pos.mpr hs) _).ne',
    Real.log_rpow hm,Real.log_rpow (inv_pos.mpr hs),Real.log_inv,Real.log_sqrt hv.le]
  field_simp
  ring

omit [IsProbabilityMeasure μ] in
private theorem lp_of_moment {Y : Ω → ℝ} {δ : ℝ} (hδ : 0 < δ) (hY : Measurable Y)
    (h : Integrable (fun ω => |Y ω|^δ) μ) : MemLp Y (ENNReal.ofReal δ) μ := by
  apply (integrable_norm_rpow_iff hY.aestronglyMeasurable (ENNReal.ofReal_ne_zero_iff.mpr hδ) ENNReal.ofReal_ne_top).mp
  simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hδ.le] using h

omit [IsProbabilityMeasure μ] in
private theorem moment_of_lp {Y : Ω → ℝ} {δ : ℝ} (hδ : 0 < δ) (hY : MemLp Y (ENNReal.ofReal δ) μ) :
    Integrable (fun ω => |Y ω|^δ) μ := by
  simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hδ.le] using
    (integrable_norm_rpow_iff hY.aestronglyMeasurable (ENNReal.ofReal_ne_zero_iff.mpr hδ) ENNReal.ofReal_ne_top).mpr hY

/-- Uniform cost of replacing raw moments by moments about the mean. -/
theorem centered_moment_le {Y : Ω → ℝ} {δ : ℝ} (hδ : 2 < δ) (h3 : δ ≤ 3) (hm : Measurable Y)
    (hY : Integrable (fun ω => |Y ω|^δ) μ) :
    (∫ ω, |Y ω-∫ t, Y t ∂μ|^δ ∂μ) ≤ 8*∫ ω, |Y ω|^δ ∂μ := by
  have h1 : 1 ≤ δ := by linarith
  have h0 : 0 < δ := by linarith
  let a := ∫ t, Y t ∂μ
  have hlp := lp_of_moment h0 hm hY
  have hI := hlp.integrable (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1)
  have hj := (convexOn_rpow h1).map_integral_le (Real.continuous_rpow_const h0.le).continuousOn isClosed_Ici
    (f := fun ω => |Y ω|) (Filter.Eventually.of_forall fun ω => abs_nonneg (Y ω)) hI.abs hY
  have hr : |a|^δ ≤ ∫ ω, |Y ω|^δ ∂μ := by
    apply le_trans (Real.rpow_le_rpow (abs_nonneg _) (norm_integral_le_integral_norm (μ := μ) Y) h0.le) hj
  have hcent : MemLp (fun ω => Y ω-a) (ENNReal.ofReal δ) μ := hlp.sub (memLp_const _)
  have hc : (2:ℝ)^(δ-1) ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by norm_num
  have hpt (ω : Ω) : |Y ω-a|^δ ≤ 4*(|Y ω|^δ + |a|^δ) := by
    apply le_trans (Real.rpow_le_rpow (abs_nonneg _) (abs_sub _ _) h0.le)
    have h := NNReal.rpow_add_le_mul_rpow_add_rpow (⟨|Y ω|,abs_nonneg _⟩ : ℝ≥0) ⟨|a|,abs_nonneg _⟩ h1
    have h' : (|Y ω|+|a|)^δ ≤ (2:ℝ)^(δ-1) * (|Y ω|^δ+|a|^δ) := by exact_mod_cast h
    exact h'.trans (mul_le_mul_of_nonneg_right hc (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)))
  have hx := integral_mono (moment_of_lp h0 hcent) ((hY.add (integrable_const (|a|^δ))).const_mul 4) hpt
  change (∫ ω, |Y ω-a|^δ ∂μ) ≤ ∫ ω, 4*(|Y ω|^δ + |a|^δ) ∂μ at hx
  rw [integral_const_mul, integral_add hY (integrable_const _), integral_const,measureReal_univ_eq_one,one_smul] at hx
  change (∫ ω, |Y ω-a|^δ ∂μ) ≤ _
  linarith only [hr,hx]

theorem normalized_raw_bound {m : ℕ} (G : Neighborhoods ι m) (hm : 0 < m)
    (Y : ι → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hG : IsDependencyGraph G μ Y)
    {δ : ℝ} (h2 : 2 < δ) (h3 : δ ≤ 3) (hM : ∀ i, Integrable (fun ω => |Y i ω|^δ) μ)
    (hv : 0 < variance (total Y) μ) :
    CDFBound μ (standardized μ (total Y))
      (min 1 (2000000*(m:ℝ)^(δ-1)*(Real.sqrt (variance (total Y) μ))⁻¹^δ*momentSum μ Y δ)) := by
  let S := total Y
  let σ := Real.sqrt (variance S μ)
  let c := σ⁻¹
  let a := fun i => ∫ ω, Y i ω ∂μ
  let X := fun i ω => c*(Y i ω-a i)
  have h0 : 0 < δ := by linarith
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hv)
  have hlp i := lp_of_moment h0 (hY i) (hM i)
  have ht i : MemLp (Y i) 2 μ := (hlp i).mono_exponent (by
    rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal h2.le)
  have hI i := (ht i).integrable (by norm_num)
  have hXm i : Measurable (X i) := ((hY i).sub_const _).const_mul _
  have hXlp i : MemLp (X i) (ENNReal.ofReal δ) μ := ((hlp i).sub (memLp_const _)).const_mul _
  have hsum : total X = fun ω => c*(S ω-∫ t, S t ∂μ) := by
    funext ω
    simp [X,S,total,a,← mul_sum,sum_sub_distrib,integral_finset_sum univ (fun i _ => hI i)]
  have hn : NormalizedFamily G μ X := by
    refine ⟨hXm,fun i => ((ht i).sub (memLp_const _)).const_mul _, ?_, ?_, ?_⟩
    · intro i
      simp only [X,integral_const_mul,integral_sub (hI i) (integrable_const _),integral_const,
        measureReal_univ_eq_one,one_smul,a,sub_self,mul_zero]
    · have hS : MemLp S 2 μ := memLp_finset_sum univ (fun i _ => ht i)
      rw [hsum,variance_mul,variance_sub_const hS.aestronglyMeasurable]
      dsimp only [c,σ]
      rw [inv_pow,Real.sq_sqrt hv.le,inv_mul_cancel₀ hv.ne']
    · intro s t hs
      let f (s : Finset ι) := fun (p : s → ℝ) (i : s) => c*(p i-a i)
      have hf s : Measurable (f s) := by dsimp [f]; fun_prop
      exact (hG s t hs).comp (hf s) (hf t)
  have hbase := janisch_lehericy G X hm hn δ h2 h3 (fun i => moment_of_lp h0 (hXlp i))
  have hW : total X = standardized μ S := by
    rw [hsum]; funext ω; simp [standardized,c,σ,div_eq_inv_mul]
  rw [hW] at hbase
  apply hbase.mono
  apply min_le_min_left
  have hb i : (∫ ω, |X i ω|^δ ∂μ) ≤ c^δ*(8*∫ ω, |Y i ω|^δ ∂μ) := by
    simp only [X,abs_mul,abs_of_pos hc,Real.mul_rpow hc.le (abs_nonneg _),integral_const_mul]
    exact mul_le_mul_of_nonneg_left (centered_moment_le h2 h3 (hY i) (hM i)) (Real.rpow_nonneg hc.le _)
  have hs := sum_le_sum (s := univ) (fun i _ => hb i)
  simp only [← mul_sum] at hs
  have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 250000*(m:ℝ)^(δ-1) by positivity)
  change _ ≤ 2000000*(m:ℝ)^(δ-1)*c^δ*(∑ i, ∫ ω, |Y i ω|^δ ∂μ)
  linarith only [h]

/-- Translate a simple graph to the closed neighborhoods used by the proof. -/
def closedGraph (g : SimpleGraph ι) [DecidableRel g.Adj] : Neighborhoods ι (g.maxDegree+1) where
  near i := insert i (g.neighborFinset i)
  self_mem _ := mem_insert_self _ _
  symm_mem i j := by
    simp only [Finset.mem_insert,SimpleGraph.mem_neighborFinset]
    rw [eq_comm,g.adj_comm]
  card_le i := by simpa [card_insert_of_notMem, g.notMem_neighborFinset_self, SimpleGraph.card_neighborFinset_eq_degree]
    using Nat.add_le_add_right (g.degree_le_maxDegree i) 1

/-- Independent blocks indexed by disjoint vertex sets with no connecting edge. -/
def GraphDependency (g : SimpleGraph ι) (μ : Measure Ω) (Y : ι → Ω → ℝ) : Prop :=
  ∀ s t : Finset ι, Disjoint s t → (∀ i ∈ s, ∀ j ∈ t, ¬g.Adj i j) →
    IndepFun (block Y s) (block Y t) μ

/-- Convert the normalized bound to the raw-moment and graph notation of the paper. -/
theorem cdfBound_xi (g : SimpleGraph ι) [DecidableRel g.Adj] (Y : ι → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hG : GraphDependency g μ Y)
    {δ : ℝ} (h2 : 2 < δ) (h3 : δ ≤ 3) (hM : ∀ i, Integrable (fun ω => |Y i ω|^δ) μ)
    (hv : 0 < variance (total Y) μ) :
    let N : ℝ := Fintype.card ι
    let m : ℝ := (g.maxDegree+1 : ℕ)
    let A := momentSum μ Y δ
    let v := variance (total Y) μ
    CDFBound μ (standardized μ (total Y))
      (min 1 (2000000*(xi N m A v δ)^(-δ)*(m/N)^((δ-2)/2))) := by
  dsimp only
  let m := g.maxDegree+1
  have hd : IsDependencyGraph (closedGraph g) μ Y := by
    intro s t hs
    apply hG
    · exact Finset.disjoint_left.mpr (fun i hi hi' => hs i hi i hi' ((closedGraph g).self_mem i))
    · intro i hi j hj hadj
      exact hs i hi j hj (mem_insert_of_mem ((g.mem_neighborFinset _ _).mpr hadj))
  have hr := normalized_raw_bound (closedGraph g) (Nat.succ_pos _) Y hY hd h2 h3 hM hv
  have hA : 0 ≤ momentSum μ Y δ := sum_nonneg (fun i _ => integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  rcases eq_or_lt_of_le hA with hz | hp
  · apply hr.mono
    rw [← hz,mul_zero]
    apply min_le_min_left
    unfold xi
    positivity
  · have hN : 0 < Fintype.card ι := by
      by_contra! h
      have hi : IsEmpty ι := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
      simp [momentSum] at hp
    have h := xi_identity (N := (Fintype.card ι:ℝ)) (m := (m:ℝ)) (A := momentSum μ Y δ)
      (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr (Nat.succ_pos _)) hp hv (by linarith : 0 < δ)
    apply hr.mono
    apply min_le_min_left
    change 2000000 * (m:ℝ)^(δ-1) * (Real.sqrt (variance (total Y) μ))⁻¹^δ * momentSum μ Y δ ≤ _
    rw [mul_assoc 2000000 ((xi _ _ _ _ _)^(-δ)),h]
    exact le_of_eq (by ring)

end JanischLehericy
