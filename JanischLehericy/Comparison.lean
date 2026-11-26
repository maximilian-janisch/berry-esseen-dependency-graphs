import JanischLehericy.Interval
import JanischLehericy.Moments

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace JanischLehericy

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Apply an interval bound for a deterministic radius to an independent,
randomly weighted interval. The upper bound can depend on the pair. -/
theorem independent_interval_le {Y : Ω → S} {V : Ω → ℝ}
    (hY : Measurable Y) (hV : Measurable V) (hi : IndepFun Y V μ)
    (w q r : S → ℝ) (hw : Measurable w) (hq : Measurable q) (hr : Measurable r)
    (hw0 : ∀ y, 0 ≤ w y) (hq0 : ∀ y, 0 ≤ q y) (u : ℝ)
    (hwi : Integrable (fun ω => w (Y ω)) μ) (hqi : Integrable (fun ω => q (Y ω)) μ)
    (hp : ∀ y, w y * μ.real {ω | |V ω-u| ≤ r y} ≤ q y) :
    (∫ ω, if |V ω-u| ≤ r (Y ω) then w (Y ω) else 0 ∂μ) ≤ ∫ ω, q (Y ω) ∂μ := by
  classical
  let E := {ω | |V ω-u| ≤ r (Y ω)}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) (hr.comp hY)
  have hI : Integrable (fun ω => if |V ω-u| ≤ r (Y ω) then w (Y ω) else 0) μ := hwi.indicator hE
  have h0 : 0 ≤ᵐ[μ] (fun ω => if |V ω-u| ≤ r (Y ω) then w (Y ω) else 0) :=
    Filter.Eventually.of_forall (fun ω => by dsimp; split_ifs <;> simp [hw0])
  have heq := weighted_random_interval hY hV hi (fun y => ENNReal.ofReal (w y))
    hw.ennreal_ofReal r hr u
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun ω => hq0 (Y ω)))).mp
  rw [ofReal_integral_eq_lintegral_ofReal hI h0,
    ofReal_integral_eq_lintegral_ofReal hqi (Filter.Eventually.of_forall (fun ω => hq0 (Y ω)))]
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (w (Y ω)) * (if |V ω-u| ≤ r (Y ω) then 1 else 0) ∂μ :=
      lintegral_congr fun ω => by split_ifs <;> simp
    _ = _ := heq
    _ ≤ ∫⁻ y, ENNReal.ofReal (q y) ∂(μ.map Y) := by
      apply lintegral_mono
      intro y
      have hmeas : MeasurableSet {x : ℝ | |x-u| ≤ r y} := measurableSet_le (by fun_prop) measurable_const
      change ENNReal.ofReal (w y) * (μ.map V) {x | |x-u| ≤ r y} ≤ ENNReal.ofReal (q y)
      rw [Measure.map_apply hV hmeas]
      have h := ENNReal.ofReal_le_ofReal (hp y)
      rwa [ENNReal.ofReal_mul (hw0 y), measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
    _ = _ := lintegral_map hq.ennreal_ofReal hY

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable {G : Neighborhoods ι m} {X : ι → Ω → ℝ}

def pairError (G : Neighborhoods ι m) (μ : Measure Ω) (X : ι → Ω → ℝ)
    (α u : ℝ) (ω : Ω) : ℝ :=
  let a := fun k => envelope μ (X k) ω
  pairs G (fun i j => a i*a j*rampBound α (total X ω) u (radius G a i + radius G a j))

omit [IsProbabilityMeasure μ] in
/-- A measurable nonnegative multiplier bounded by one preserves integrability. -/
theorem integrable_cutoff {g b : Ω → ℝ} (hg : Integrable g μ) (hg0 : ∀ ω, 0 ≤ g ω)
    (hb : Measurable b) (hb0 : ∀ ω, 0 ≤ b ω) (hb1 : ∀ ω, b ω ≤ 1) :
    Integrable (fun ω => g ω * b ω) μ := by
  apply hg.mono' (hg.aestronglyMeasurable.mul hb.aestronglyMeasurable)
  filter_upwards with ω
  change |g ω * b ω| ≤ g ω
  rw [abs_of_nonneg (mul_nonneg (hg0 ω) (hb0 ω))]
  exact mul_le_of_le_one_right (hg0 ω) (hb1 ω)

/-- Expected adjacent-pair error controlled by deterministic interval bounds on
the outside sums, uniformly in the location of the smoothed step. -/
theorem pairError_bound (H : NormalizedFamily G μ X) (hm : 0 < m)
    {α η : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hη : 0 ≤ η)
    (hV : ∀ i j u h, 0 ≤ h →
      μ.real {ω | |outsideSum G X i j ω-u| ≤ h} ≤ min 1 (2*h) + η) (u : ℝ) :
    (∫ ω, pairError G μ X α u ω ∂μ) ≤ 8 * ((28+4*η/α) * (8*beta μ m X)) := by
  classical
  let a := fun i ω => envelope μ (X i) ω
  let L := fun i j ω => pairScale m (fun k => a k ω) i j
  let F := fun i j ω => a i ω*a j ω * min 1 (L i j ω)
  let T := fun i j ω => if |outsideSum G X i j ω-u| ≤ α+10*L i j ω
    then a i ω*a j ω * min 1 (4*L i j ω/α) else 0
  let C := 28+4*η/α
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha i ω : 0 ≤ a i ω := envelope_nonneg _ _
  have hL i j ω : 0 ≤ L i j ω := mul_nonneg (Nat.cast_nonneg _) (le_max_of_le_left (ha i ω))
  have ham i : Measurable (a i) := (H.measurable i).abs.max measurable_const
  have hLm i j : Measurable (L i j) := ((ham i).max (ham j)).const_mul _
  have hprod i j : Integrable (fun ω => a i ω*a j ω) μ :=
    (envelope_memLp (H.squareIntegrable i)).integrable_mul (envelope_memLp (H.squareIntegrable j))
  have hFi i j : Integrable (F i j) μ := integrable_cutoff (hprod i j)
    (fun ω => mul_nonneg (ha i ω) (ha j ω)) (measurable_const.min (hLm i j))
    (fun ω => le_min zero_le_one (hL i j ω)) (fun _ => min_le_left _ _)
  have hBi i j : Integrable (fun ω => a i ω*a j ω*min 1 (4*L i j ω/α)) μ :=
    integrable_cutoff (hprod i j) (fun ω => mul_nonneg (ha i ω) (ha j ω))
      (measurable_const.min (((hLm i j).const_mul 4).div_const α))
      (fun ω => le_min zero_le_one (div_nonneg (by linarith [hL i j ω]) hα.le)) (fun _ => min_le_left _ _)
  have hVm i j : Measurable (outsideSum G X i j) := Finset.measurable_sum _ (fun k _ => H.measurable k)
  have hTi i j : Integrable (T i j) μ := (hBi i j).indicator
    (measurableSet_le ((hVm i j).sub_const u).abs (((hLm i j).const_mul 10).const_add α))
  have hpair i j : (∫ ω, T i j ω ∂μ) ≤ C * ∫ ω, F i j ω ∂μ := by
    let Y := fun ω => (X i ω,X j ω)
    let ai := fun p : ℝ × ℝ => max |p.1| (rms μ (X i))
    let aj := fun p : ℝ × ℝ => max |p.2| (rms μ (X j))
    let l := fun p => (m:ℝ)*max (ai p) (aj p)
    let w := fun p => ai p*aj p*min 1 (4*l p/α)
    let q := fun p => C*(ai p*aj p*min 1 (l p))
    have hai p : 0 ≤ ai p := (abs_nonneg _).trans (le_max_left _ _)
    have haj p : 0 ≤ aj p := (abs_nonneg _).trans (le_max_left _ _)
    have hl p : 0 ≤ l p := mul_nonneg (Nat.cast_nonneg _) (le_max_of_le_left (hai p))
    have hw p : 0 ≤ w p := mul_nonneg (mul_nonneg (hai p) (haj p))
      (le_min zero_le_one (div_nonneg (by linarith [hl p]) hα.le))
    have hq p : 0 ≤ q p := mul_nonneg hC (mul_nonneg (mul_nonneg (hai p) (haj p)) (le_min zero_le_one (hl p)))
    rw [← integral_const_mul]
    apply independent_interval_le (Y := Y) ((H.measurable i).prodMk (H.measurable j)) (hVm i j)
      (pair_independent_outside G H.dependency i j) w q (fun p => α+10*l p)
      (by dsimp [w,l,ai,aj]; fun_prop) (by dsimp [q,l,ai,aj]; fun_prop)
      (by dsimp [l,ai,aj]; fun_prop) hw hq u (hBi i j) ((hFi i j).const_mul C)
    intro p
    have h := hV i j u (α+10*l p) (by linarith [hl p])
    have h1 := mul_le_mul_of_nonneg_left h (hw p)
    have h2 := mul_le_mul_of_nonneg_left (ramp_interval_product hα hα1 (hl p) hη)
      (mul_nonneg (hai p) (haj p))
    dsimp only [q,w,C] at *
    linarith only [h1,h2]
  have hpt ω : pairError G μ X α u ω ≤ 8 * pairs G (fun i j => T i j ω) := by
    have h := adjacent_pair_inequality G hm (fun i => X i ω) (fun i => a i ω)
      (fun i => le_max_left _ _) α u hα
    refine h.trans (mul_le_mul_of_nonneg_left (pairs_le G (fun i j _ => ?_)) (by norm_num))
    dsimp only [T, L, outsideSum, outside]
    split_ifs <;> simp
  have hnon ω : 0 ≤ pairError G μ X α u ω :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (mul_nonneg (ha i ω) (ha j ω))
      (rampBound_nonneg hα (add_nonneg (sum_nonneg fun k _ => ha k ω) (sum_nonneg fun k _ => ha k ω)))
  have hsum := integral_mono_of_nonneg (Filter.Eventually.of_forall hnon)
    ((integrable_finset_sum univ (fun i _ => integrable_finset_sum (G.near i) (fun j _ => hTi i j))).const_mul 8)
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hsum
  simp only [integral_finset_sum univ (fun i _ => integrable_finset_sum (G.near i) (fun j _ => hTi i j)),
    integral_finset_sum _ (fun j _ => hTi _ j)] at hsum
  have hs := pairs_le G (fun i j _ => hpair i j)
  rw [pairs_mul] at hs
  have hb : pairs G (fun i j => ∫ ω, F i j ω ∂μ) ≤ 8*beta μ m X := pair_moment_bound G hm H.squareIntegrable
  exact hsum.trans (mul_le_mul_of_nonneg_left (hs.trans (mul_le_mul_of_nonneg_left hb hC)) (by norm_num))

end JanischLehericy
