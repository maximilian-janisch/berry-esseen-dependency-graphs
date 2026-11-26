import JanischLehericy.Budget
import JanischLehericy.Dependence

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace JanischLehericy

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable {μ : Measure Ω}
variable {m : ℕ} {X : ι → Ω → ℝ}

/-- Root mean square about zero. -/
def rms (μ : Measure Ω) (v : Ω → ℝ) : ℝ := Real.sqrt (∫ ω, v ω ^ 2 ∂μ)

def envelope (μ : Measure Ω) (v : Ω → ℝ) (ω : Ω) : ℝ := max |v ω| (rms μ v)

theorem rms_sq (v : Ω → ℝ) : (rms μ v)^2 = ∫ ω, v ω^2 ∂μ :=
  Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)

theorem envelope_nonneg (v : Ω → ℝ) (ω : Ω) : 0 ≤ envelope μ v ω :=
  (abs_nonneg _).trans (le_max_left _ _)

variable [IsProbabilityMeasure μ]

theorem envelope_memLp {v : Ω → ℝ} (hv : MemLp v 2 μ) :
    MemLp (envelope μ v) 2 μ := hv.norm.sup (memLp_const _)

theorem ell_envelope (m : ℕ) {v : Ω → ℝ} (hv : MemLp v 2 μ) :
    (∫ ω, ell (m * envelope μ v ω) ∂μ) ≤ 4 * ∫ ω, ell (m * |v ω|) ∂μ := by
  let s : ℝ := m * rms μ v
  let t : Ω → ℝ := fun ω => m * |v ω|
  have ht ω : 0 ≤ t ω := mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have ht2 : Integrable (fun ω => (t ω)^2) μ := by
    simpa [t, mul_pow, sq_abs] using hv.integrable_sq.const_mul ((m:ℝ)^2)
  have hsq : (∫ ω, (t ω)^2 ∂μ) = s^2 := by
    simp [t, s, mul_pow, sq_abs, integral_const_mul, rms_sq]
  have he : Integrable (fun ω => ell (t ω)) μ := integrable_ell μ hv m
  have hp := integral_mono (ht2.mul_const (min 1 s))
    ((he.const_mul 2).add (integrable_const (ell s / 4))) (fun ω => envelope_point (ht ω) hs)
  simp only [Pi.add_apply, integral_add (he.const_mul 2) (integrable_const _),
    integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul, integral_mul_const, hsq] at hp
  have hse : ell s ≤ 3 * ∫ ω, ell (t ω) ∂μ := by
    change ell s ≤ 2 * (∫ ω, ell (t ω) ∂μ) + ell s / 4 at hp
    have hn : 0 ≤ ∫ ω, ell (t ω) ∂μ := integral_nonneg fun ω => ell_nonneg (ht ω)
    linarith only [hn, hp]
  have hmax ω : ell (m * envelope μ v ω) ≤ ell (t ω) + ell s := by
    unfold envelope
    rcases le_total (rms μ v) |v ω| with h | h
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (ell_nonneg hs)
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (ell_nonneg (ht ω))
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
    ell_nonneg (mul_nonneg (Nat.cast_nonneg m) (envelope_nonneg v ω)))
    (he.add (integrable_const (ell s))) (Filter.Eventually.of_forall hmax)
  simp only [Pi.add_apply, integral_add he (integrable_const _)] at h
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at h
  change _ ≤ 4 * ∫ ω, ell (t ω) ∂μ
  linarith

theorem pair_truncation {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x*y*min 1 (max x y) ≤ ell x + ell y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hy) (le_min zero_le_one hy)
    dsimp [ell] at *
    nlinarith only [this, ell_nonneg hx, show ell x = x^2 * min 1 x from rfl]
  · rw [max_eq_left h]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hx) (le_min zero_le_one hx)
    dsimp [ell] at *
    nlinarith only [this, ell_nonneg hy, show ell y = y^2 * min 1 y from rfl]

/-- Equation (the envelope moment bound) for all ordered adjacent pairs. -/
theorem pair_moment_bound (G : Neighborhoods ι m) (hm : 0 < m)
    (hX : ∀ i, MemLp (X i) 2 μ) :
    pairs G (fun i j => ∫ ω, envelope μ (X i) ω * envelope μ (X j) ω *
      min 1 (pairScale m (fun k => envelope μ (X k) ω) i j) ∂μ) ≤ 8 * beta μ m X := by
  let a := fun i => envelope μ (X i)
  let B := fun i => ∫ ω, ell (m * a i ω) ∂μ
  have hB i : 0 ≤ B i := integral_nonneg fun ω =>
    ell_nonneg (mul_nonneg (Nat.cast_nonneg _) (envelope_nonneg _ _))
  have ha i : Integrable (fun ω => ell (m * a i ω)) μ := by
    simpa [a, abs_of_nonneg (envelope_nonneg (μ := μ) _ _)] using integrable_ell μ (envelope_memLp (hX i)) m
  let F := fun i j ω => a i ω * a j ω * min 1 (pairScale m (fun k => a k ω) i j)
  have hpt i j ω : (m : ℝ)^2 * F i j ω ≤ ell (m*a i ω) + ell (m*a j ω) := by
    have h := pair_truncation (mul_nonneg (Nat.cast_nonneg m : 0 ≤ (m:ℝ)) (envelope_nonneg (μ := μ) (X i) ω))
      (mul_nonneg (Nat.cast_nonneg m : 0 ≤ (m:ℝ)) (envelope_nonneg (μ := μ) (X j) ω))
    rw [← mul_max_of_nonneg _ _ (Nat.cast_nonneg _)] at h
    dsimp only [F, pairScale, a]
    linarith only [h]
  have hi i j : (m : ℝ)^2 * (∫ ω, F i j ω ∂μ) ≤ B i + B j := by
    rw [← integral_const_mul, ← integral_add (ha i) (ha j)]
    apply integral_mono_of_nonneg _ ((ha i).add (ha j)) (Filter.Eventually.of_forall (hpt i j))
    filter_upwards with ω
    dsimp only [F, pairScale]
    have h1 := envelope_nonneg (μ := μ) (X i) ω
    have h2 := envelope_nonneg (μ := μ) (X j) ω
    change 0 ≤ (m:ℝ)^2 * (envelope μ (X i) ω * envelope μ (X j) ω * _)
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg h1 h2)
      (le_min zero_le_one (mul_nonneg (Nat.cast_nonneg _) (le_max_of_le_left h1))))
  have hsum := pairs_le G (f := fun i j => (m:ℝ)^2 * ∫ ω, F i j ω ∂μ)
    (g := fun i j => B i + B j) (fun i j _ => hi i j)
  rw [pairs_mul, pairs_add, pairs_swap G (fun _ j => B j)] at hsum
  have hb := pairs_row_le G B hB
  have h4 := Finset.sum_le_sum (s := univ) (fun i _ => ell_envelope m (hX i))
  rw [← mul_sum] at h4
  have hc : ∑ i, B i ≤ 4 * ∑ i, ∫ ω, ell (m * |X i ω|) ∂μ := h4
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hscaled := mul_le_mul_of_nonneg_left hc hm'.le
  change pairs G (fun i j => ∫ ω, F i j ω ∂μ) ≤ 8 * _
  unfold beta
  rw [← mul_div_assoc, le_div_iff₀ hm']
  apply le_of_mul_le_mul_left (a := (m:ℝ)) _ hm'
  linarith only [hsum, hb, hscaled]

/-- A simpler deletion estimate sufficient for the induction threshold. -/
theorem deleted_second_moment (hm : 0 < m) (hX : ∀ i, MemLp (X i) 2 μ)
    (A : Finset ι) (hA : A.card ≤ 2*m) :
    (∫ ω, (∑ i ∈ A, X i ω)^2 ∂μ) ≤ 1/16 + 16*beta μ m X := by
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hA' : (A.card:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast hA
  let b := fun i => ∫ ω, ell (m * |X i ω|) ∂μ
  have hb i : 0 ≤ b i := integral_nonneg fun ω => ell_nonneg (by positivity)
  have hi i : (m:ℝ)^2 * (∫ ω, X i ω ^ 2 ∂μ) ≤ 1/64 + 8 * b i := by
    have h := integral_mono ((hX i).integrable_sq.const_mul ((m:ℝ)^2))
      ((integrable_const (1/64:ℝ)).add ((integrable_ell μ (hX i) m).const_mul 8)) (fun ω => by
        simpa [mul_pow, sq_abs] using sq_le_truncated (t := (m:ℝ)*|X i ω|) (by positivity))
    simpa [b, integral_const_mul, integral_add (integrable_const _) ((integrable_ell μ (hX i) m).const_mul 8)] using h
  have hsum := sum_le_sum (s := A) fun i _ => hi i
  simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hsum
  have hsub := sum_le_sum_of_subset_of_nonneg (subset_univ A) (f := b) (fun i _ _ => hb i)
  have hcs ω : (∑ i ∈ A, X i ω)^2 ≤ (2*(m:ℝ)) * ∑ i ∈ A, X i ω^2 := by
    have h := sum_mul_sq_le_sq_mul_sq A (fun _ => (1:ℝ)) (fun i => X i ω)
    simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right hA' (sum_nonneg fun i _ => sq_nonneg _))
  have hs := integral_mono (memLp_finset_sum A (fun i _ => hX i)).integrable_sq
    ((integrable_finset_sum A (fun i _ => (hX i).integrable_sq)).const_mul (2*(m:ℝ))) hcs
  rw [integral_const_mul, integral_finset_sum A (fun i _ => (hX i).integrable_sq)] at hs
  have hβ : (∑ i, b i) = beta μ m X * m := (div_mul_cancel₀ _ hm'.ne').symm
  have H := mul_le_mul_of_nonneg_left hs hm'.le
  apply le_of_mul_le_mul_left (a := (m:ℝ)) _ hm'
  linarith only [H, hA', hsum, hsub, hβ]

end JanischLehericy
