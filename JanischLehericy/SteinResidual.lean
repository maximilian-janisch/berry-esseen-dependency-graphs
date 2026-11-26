import JanischLehericy.SteinIdentity

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators
noncomputable section
namespace JanischLehericy

/-- Properties of a smoothed test used in the graph calculation. -/
structure SmoothTest (α : ℝ) where
  f : ℝ → ℝ
  d : ℝ → ℝ
  ν : Measure ℝ
  finite : IsFiniteMeasure ν
  mass : ν.real Set.univ ≤ 2
  fBound : ∃ C : ℝ, ∀ x, |f x| ≤ C
  dBound : ∃ C : ℝ, ∀ x, |d x| ≤ C
  deriv : ∀ x, HasDerivAt f (d x) x
  measurable : Measurable d
  oscillation : ∀ w t s : ℝ, |w-t| ≤ s →
    |d w-d t| ≤ ∫ u, rampBound α w u s ∂ν

theorem rampBound_le_one (α w u s : ℝ) : rampBound α w u s ≤ 1 := by
  unfold rampBound
  split_ifs <;> first | exact min_le_left _ _ | norm_num

theorem measurable_ramp {S : Type*} [MeasurableSpace S] (α : ℝ) {w u s : S → ℝ}
    (hw : Measurable w) (hu : Measurable u) (hs : Measurable s) :
    Measurable (fun p => rampBound α (w p) (u p) (s p)) :=
  Measurable.ite (measurableSet_le (hw.sub hu).abs (hs.const_add α))
    (measurable_const.min (hs.div_const α)) measurable_const

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ} {G : Neighborhoods ι m}
variable {X : ι → Ω → ℝ}

omit [DecidableEq ι] in
theorem abs_pairs_le (b : ι → ι → ℝ) : |pairs G b| ≤ pairs G (fun i j => |b i j|) :=
  (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)

omit [IsProbabilityMeasure μ] in
theorem radius_bounds (i j : ι) (ω : Ω) :
    let a := fun k => envelope μ (X k) ω
    |localSum G X i ω| ≤ radius G a i + radius G a j ∧
    |total X ω - outsideSum G X i j ω| ≤ radius G a i + radius G a j := by
  let a := fun k => envelope μ (X k) ω
  have ha k : 0 ≤ a k := envelope_nonneg _ _
  have hA (A : Finset ι) : |∑ k ∈ A, X k ω| ≤ ∑ k ∈ A, a k :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => le_max_left _ _)
  refine ⟨(hA _).trans (le_add_of_nonneg_right (sum_nonneg fun k _ => ha k)), ?_⟩
  have h := sum_sdiff (Finset.subset_univ (G.near i ∪ G.near j)) (f := fun k => X k ω)
  have he : total X ω - outsideSum G X i j ω = ∑ k ∈ G.near i ∪ G.near j, X k ω := by
    dsimp [total, outsideSum, outside]
    linarith
  rw [he]
  apply (hA _).trans
  change _ ≤ (∑ k ∈ G.near i, a k) + ∑ k ∈ G.near j, a k
  have h' := sum_union_inter (s₁ := G.near i) (s₂ := G.near j) (f := a)
  linarith [show 0 ≤ ∑ k ∈ G.near i ∩ G.near j, a k from sum_nonneg fun k _ => ha k]

/-- Quantitative graph bound for a test with a finite variation measure. -/
theorem stein_residual (H : NormalizedFamily G μ X) {α : ℝ} (hα : 0 < α) (T : SmoothTest α)
    {K : ℝ} (hK : ∀ u, (∫ ω, pairError G μ X α u ω ∂μ) ≤ K) :
    |(∫ ω, T.d (total X ω) ∂μ) - ∫ ω, total X ω * T.f (total X ω) ∂μ| ≤ 6*K := by
  letI : IsFiniteMeasure T.ν := T.finite
  let W := total X
  let V := outsideSum G X
  let Y := localSum G X
  let a := fun k ω => envelope μ (X k) ω
  let A := fun i j ω => a i ω*a j ω
  let R := fun i ω => radius G (fun k => a k ω) i
  let p := fun i j ω => X i ω*X j ω
  let c := fun i j => ∫ ω, p i j ω ∂μ
  let s := fun i ω => secant T.f T.d (W ω) (Y i ω)
  let r := fun i j ω => c i j*T.d (W ω) - p i j ω*s i ω
    - c i j*T.d (V i j ω) + p i j ω*T.d (V i j ω)
  let P := fun ω u => pairError G μ X α u ω
  have hf := (continuous_iff_continuousAt.mpr (fun x => (T.deriv x).continuousAt)).measurable
  obtain ⟨B,hB⟩ := T.dBound
  obtain ⟨D,hD⟩ := T.fBound
  have hW : Measurable W := Finset.measurable_sum _ (fun k _ => H.measurable k)
  have hV i j : Measurable (V i j) := Finset.measurable_sum _ (fun k _ => H.measurable k)
  have hY i : Measurable (Y i) := Finset.measurable_sum _ (fun k _ => H.measurable k)
  have hs i : Measurable (s i) := Measurable.ite (measurableSet_eq_fun (hY i) measurable_const)
    (T.measurable.comp hW) (((hf.comp hW).sub (hf.comp (hW.sub (hY i)))).div (hY i))
  have hsB i ω : |s i ω| ≤ B := by
    obtain ⟨t,_,he⟩ := secant_witness T.deriv (W ω) (Y i ω)
    change |secant T.f T.d (W ω) (Y i ω)| ≤ B
    rw [he]
    exact hB t
  have hpi i j : Integrable (p i j) μ := (H.squareIntegrable i).integrable_mul (H.squareIntegrable j)
  have hdI {Z : Ω → ℝ} (hZ : Measurable Z) : Integrable (fun ω => T.d (Z ω)) μ :=
    (MemLp.of_bound (p := 1) (T.measurable.comp hZ).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => hB (Z ω))).integrable le_rfl
  have hps i j : Integrable (fun ω => p i j ω*s i ω) μ := by
    simpa only [mul_comm] using (hpi i j).bdd_mul (hs i).aestronglyMeasurable ⟨B,hsB i⟩
  have hpV i j : Integrable (fun ω => p i j ω*T.d (V i j ω)) μ := by
    simpa only [mul_comm] using (hpi i j).bdd_mul (T.measurable.comp (hV i j)).aestronglyMeasurable
      ⟨B,fun ω => hB _⟩
  have hr i j : Integrable (r i j) μ :=
    ((((hdI hW).const_mul _).sub (hps i j)).sub ((hdI (hV i j)).const_mul _)).add (hpV i j)
  have hrow := row_identity H T.f hf s (fun i ω => by rw [outside_self]; exact mul_secant ..)
    (fun i => MemLp.of_bound (hf.comp (hV i i)).aestronglyMeasurable D
      (Filter.Eventually.of_forall fun ω => hD _)) hps
  have hri i j : (∫ ω, r i j ω ∂μ) = c i j*(∫ ω, T.d (W ω) ∂μ) - ∫ ω, p i j ω*s i ω ∂μ := by
    dsimp only [r]
    have h1 : Integrable (fun ω => c i j*T.d (W ω) - p i j ω*s i ω) μ :=
      ((hdI hW).const_mul _).sub (hps i j)
    have h2 : Integrable (fun ω => c i j*T.d (W ω) - p i j ω*s i ω - c i j*T.d (V i j ω)) μ :=
      h1.sub ((hdI (hV i j)).const_mul _)
    rw [integral_add h2 (hpV i j), integral_sub h1 ((hdI (hV i j)).const_mul (c i j)),
      integral_sub ((hdI hW).const_mul (c i j)) (hps i j), integral_const_mul, integral_const_mul]
    have ho := outside_covariance H i j T.d T.measurable
    change (∫ ω, p i j ω*T.d (V i j ω) ∂μ) = c i j * _ at ho
    rw [ho]
    ring
  have he : (∫ ω, T.d (W ω) ∂μ) - (∫ ω, W ω*T.f (W ω) ∂μ) =
      ∫ ω, pairs G (fun i j => r i j ω) ∂μ := by
    rw [integral_pairs r hr]
    simp only [hri, pairs, sum_sub_distrib, ← Finset.sum_mul]
    change _ - _ = pairs G c * _ - pairs G _
    rw [show pairs G c = 1 from sum_pair_covariance H, one_mul, hrow]
  have ha i ω : 0 ≤ a i ω := envelope_nonneg _ _
  have hA i j ω : 0 ≤ A i j ω := mul_nonneg (ha i ω) (ha j ω)
  have hR i ω : 0 ≤ R i ω := sum_nonneg fun k _ => ha k ω
  have hPa ω u : 0 ≤ P ω u := sum_nonneg fun i _ => sum_nonneg fun j _ =>
    mul_nonneg (hA i j ω) (rampBound_nonneg hα (add_nonneg (hR i ω) (hR j ω)))
  have hPa' : 0 ≤ K := (integral_nonneg fun ω => hPa ω 0).trans (hK 0)
  let rad := fun i j ω u => rampBound α (W ω) u (R i ω + R j ω)
  have hradInt i j ω : Integrable (fun u => rad i j ω u) T.ν := by
    exact (MemLp.of_bound (p := 1) (measurable_ramp α measurable_const measurable_id measurable_const).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (rampBound_nonneg hα (add_nonneg (hR i ω) (hR j ω)))]
        exact rampBound_le_one ..)).integrable le_rfl
  have hpt ω : |pairs G (fun i j => r i j ω)| ≤ 3*∫ u, P ω u ∂T.ν := by
    have hq i j : |r i j ω| ≤ 3*(A i j ω*(∫ u, rad i j ω u ∂T.ν)) := by
      let J := ∫ u, rad i j ω u ∂T.ν
      have hJ : 0 ≤ J := integral_nonneg fun _ => rampBound_nonneg hα (add_nonneg (hR i ω) (hR j ω))
      have hx := radius_bounds (μ := μ) (G := G) (X := X) i j ω
      have hdiff : |T.d (W ω)-T.d (V i j ω)| ≤ J := T.oscillation _ _ _ hx.2
      obtain ⟨t,ht,he'⟩ := secant_witness T.deriv (W ω) (Y i ω)
      have hsec : |T.d (W ω)-s i ω| ≤ J := by
        change |T.d (W ω)-secant T.f T.d (W ω) (Y i ω)| ≤ J
        rw [he']
        exact T.oscillation _ _ _ (ht.trans hx.1)
      have hc : |c i j| ≤ A i j ω := abs_pair_covariance H i j ω
      have hp : |p i j ω| ≤ A i j ω := by
        rw [show p i j ω = X i ω*X j ω from rfl,abs_mul]
        exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (abs_nonneg _) (ha i ω)
      have hcp : |c i j-p i j ω| ≤ 2*A i j ω := (abs_sub _ _).trans (by linarith)
      have heq : r i j ω = (c i j - p i j ω)*(T.d (W ω)-T.d (V i j ω))
          + p i j ω*(T.d (W ω)-s i ω) := by dsimp only [r]; ring
      rw [heq]
      apply (abs_add_le ..).trans
      rw [abs_mul,abs_mul]
      have h1 := mul_le_mul hcp hdiff (abs_nonneg _) (by linarith [hA i j ω])
      have h2 := mul_le_mul hp hsec (abs_nonneg _) (hA i j ω)
      change _ ≤ 3*(A i j ω*J)
      linarith only [h1,h2]
    apply (abs_pairs_le _).trans
    apply (pairs_le G (fun i j _ => hq i j)).trans_eq
    rw [pairs_mul]
    congr 1
    have h := integral_pairs (G := G) (μ := T.ν) (fun i j u => A i j ω*rad i j ω u)
      (fun i j => (hradInt i j ω).const_mul _)
    simpa only [integral_const_mul] using h.symm
  have hAI i j : Integrable (A i j) μ := (envelope_memLp (H.squareIntegrable i)).integrable_mul
    (envelope_memLp (H.squareIntegrable j))
  have ham k : Measurable (a k) := (H.measurable k).abs.max measurable_const
  have hRm i : Measurable (R i) := Finset.measurable_sum _ (fun k _ => ham k)
  have hprod : Integrable (Function.uncurry P) (μ.prod T.ν) := by
    apply integrable_pairs (G := G) (fun i j (p : Ω × ℝ) => A i j p.1*rad i j p.1 p.2)
    intro i j
    exact integrable_cutoff ((hAI i j).comp_fst T.ν) (fun p => hA i j p.1)
      (measurable_ramp α (hW.comp measurable_fst) measurable_snd (((hRm i).add (hRm j)).comp measurable_fst))
      (fun p => rampBound_nonneg hα (add_nonneg (hR i p.1) (hR j p.1))) (fun _ => rampBound_le_one ..)
  change |(∫ ω, T.d (W ω) ∂μ) - ∫ ω, W ω*T.f (W ω) ∂μ| ≤ _
  rw [he]
  have hbound := norm_integral_le_of_norm_le (f := fun ω => pairs G (fun i j => r i j ω)) (hprod.integral_prod_left.const_mul 3)
    (Filter.Eventually.of_forall hpt)
  change |∫ ω, pairs G (fun i j => r i j ω) ∂μ| ≤ ∫ ω, 3*(∫ u, P ω u ∂T.ν) ∂μ at hbound
  rw [integral_const_mul, integral_integral_swap hprod] at hbound
  have hupper := integral_mono hprod.integral_prod_right (integrable_const K) hK
  rw [integral_const, smul_eq_mul] at hupper
  change (∫ u, ∫ ω, P ω u ∂μ ∂T.ν) ≤ T.ν.real Set.univ * K at hupper
  exact hbound.trans (by nlinarith only [hupper,mul_le_mul_of_nonneg_right T.mass hPa'])

end JanischLehericy
