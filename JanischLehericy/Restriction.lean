import JanischLehericy.Moments
import JanischLehericy.Statement

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace JanischLehericy

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
variable {m : ℕ} {G : Neighborhoods ι m} {μ : Measure Ω} {X : ι → Ω → ℝ}

def induced (G : Neighborhoods ι m) (A : Finset ι) : Neighborhoods A m where
  near i := (G.near i).subtype (· ∈ A)
  self_mem i := mem_subtype.mpr (G.self_mem _)
  symm_mem i j := by simp only [mem_subtype]; exact G.symm_mem i j
  card_le i := by rw [card_subtype]; exact (card_filter_le _ _).trans (G.card_le _)

def scaled (A : Finset ι) (c : ℝ) (X : ι → Ω → ℝ) (i : A) (ω : Ω) : ℝ := c * X i ω

theorem dependency_induced (h : IsDependencyGraph G μ X) (A : Finset ι) (c : ℝ) :
    IsDependencyGraph (induced G A) μ (scaled A c X) := by
  intro s t hsep
  let e := Function.Embedding.subtype (· ∈ A)
  have hj : ∀ i ∈ s.map e, ∀ j ∈ t.map e, j ∉ G.near i := by
    intro i hi j hj
    obtain ⟨k,hk,rfl⟩ := mem_map.mp hi
    obtain ⟨l,hl,rfl⟩ := mem_map.mp hj
    exact fun hn => hsep k hk l hl (mem_subtype.mpr hn)
  let proj (s : Finset A) (v : s.map e → ℝ) (k : s) : ℝ :=
    c * v ⟨e k.val, mem_map_of_mem _ k.property⟩
  have hp (s : Finset A) : Measurable (proj s) := by dsimp [proj]; fun_prop
  exact (h _ _ hj).comp (hp s) (hp t)

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] in
theorem total_scaled (A : Finset ι) (c : ℝ) (ω : Ω) :
    total (scaled A c X) ω = c * ∑ i ∈ A, X i ω := by
  change (∑ i : A, c * X i ω) = _
  rw [← mul_sum]
  exact congrArg (c * ·) (sum_attach A (fun i => X i ω))

variable [IsProbabilityMeasure μ]

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
theorem beta_scaled (A : Finset ι) (hm : 0 < m) {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 2)
    (hX : ∀ i, MemLp (X i) 2 μ) :
    beta μ m (scaled A c X) ≤ 8 * beta μ m X := by
  let b (i : ι) := ∫ ω, ell (m * |X i ω|) ∂μ
  have hi (i : A) : (∫ ω, ell (m * |scaled A c X i ω|) ∂μ) ≤ 8 * b i := by
    rw [← integral_const_mul]
    apply integral_mono (integrable_ell μ ((hX i).const_mul c) m) ((integrable_ell μ (hX i) m).const_mul 8)
    intro ω
    simp only [abs_mul, abs_of_nonneg hc]
    rw [mul_left_comm]
    exact ell_scale_le (by positivity) hc hc2
  have hs := sum_le_sum (s := univ) (fun (i : A) _ => hi i)
  have he : (∑ i : A, b i) = ∑ i ∈ A, b i := sum_attach A b
  rw [← mul_sum, he] at hs
  have hall : ∑ i ∈ A, b i ≤ ∑ i, b i := sum_le_sum_of_subset_of_nonneg (subset_univ _)
    (fun i _ _ => integral_nonneg fun ω => ell_nonneg (by positivity))
  unfold beta
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (hs.trans (mul_le_mul_of_nonneg_left hall (by norm_num))) (Nat.cast_nonneg _)

theorem beta_pos (hm : 0 < m) (H : NormalizedFamily G μ X) : 0 < beta μ m X := by
  by_contra! hn
  have hz := le_antisymm hn (beta_nonneg μ m X)
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have ht : (∑ i, ∫ ω, ell (m * |X i ω|) ∂μ) = 0 := by
    unfold beta at hz
    exact (div_eq_zero_iff.mp hz).resolve_right hm'.ne'
  have hi := (sum_eq_zero_iff_of_nonneg (fun i _ => integral_nonneg (μ := μ)
    (fun ω => ell_nonneg (mul_nonneg hm'.le (abs_nonneg (X i ω)))))).mp ht
  have hnull i : ∀ᵐ ω ∂μ, X i ω = 0 := by
    have hz' := (integral_eq_zero_iff_of_nonneg (fun ω =>
      ell_nonneg (mul_nonneg hm'.le (abs_nonneg (X i ω)))) (integrable_ell μ (H.squareIntegrable i) m)).mp
      (hi i (mem_univ _))
    filter_upwards [hz'] with ω hω
    by_contra! hx
    have hpos := mul_pos hm' (abs_pos.mpr hx)
    have : 0 < ell (m * |X i ω|) := mul_pos (sq_pos_of_pos hpos) (lt_min zero_lt_one hpos)
    exact this.ne' hω
  have htot : (fun ω => (total X ω)^2) =ᵐ[μ] (fun _ => 0) := by
    filter_upwards [ae_all_iff.mpr hnull] with ω hω
    simp [total, hω]
  have h := total_second_moment H
  rw [integral_congr_ae htot, integral_zero] at h
  norm_num at h

/-- A variance-one sum with small budget retains standard deviation greater
than one half outside either pair of neighborhoods. -/
theorem outside_rms_gt_half (hm : 0 < m) (H : NormalizedFamily G μ X)
    (hβ : beta μ m X < 1/50000) (i j : ι) : 1/2 < rms μ (outsideSum G X i j) := by
  let A := G.near i ∪ G.near j
  let D := fun ω => ∑ k ∈ A, X k ω
  let V := outsideSum G X i j
  have hd := deleted_second_moment hm H.squareIntegrable A (outside_card_deleted G i j)
  have hv : MemLp V 2 μ := memLp_finset_sum _ (fun k _ => H.squareIntegrable k)
  have hD : MemLp D 2 μ := memLp_finset_sum A (fun k _ => H.squareIntegrable k)
  have he ω : V ω + D ω = total X ω := sum_sdiff (subset_univ A) (f := fun k => X k ω)
  have h := integral_mono (memLp_finset_sum univ (fun k _ => H.squareIntegrable k)).integrable_sq
    ((hv.integrable_sq.const_mul 2).add (hD.integrable_sq.const_mul 2)) (fun ω => by
      change (total X ω)^2 ≤ 2*(V ω)^2 + 2*(D ω)^2
      rw [← he]
      nlinarith [sq_nonneg (V ω-D ω)])
  change (∫ ω, (total X ω)^2 ∂μ) ≤ ∫ ω, 2*(V ω)^2 + 2*(D ω)^2 ∂μ at h
  rw [total_second_moment H, integral_add (hv.integrable_sq.const_mul 2) (hD.integrable_sq.const_mul 2),
    integral_const_mul, integral_const_mul] at h
  change (∫ ω, (D ω)^2 ∂μ) ≤ _ at hd
  apply (Real.lt_sqrt (by norm_num)).mpr
  change (1/2:ℝ)^2 < ∫ ω, (V ω)^2 ∂μ
  linarith only [h,hd,hβ]

theorem normalized_outside (H : NormalizedFamily G μ X) (i j : ι)
    (hs : 0 < rms μ (outsideSum G X i j)) :
    NormalizedFamily (induced G (outside G i j)) μ
      (scaled (outside G i j) (rms μ (outsideSum G X i j))⁻¹ X) := by
  let A := outside G i j
  let V := outsideSum G X i j
  let c := (rms μ V)⁻¹
  refine ⟨fun k => (H.measurable k).const_mul c, fun k => (H.squareIntegrable k).const_mul c, ?_, ?_,
    dependency_induced H.dependency A c⟩
  · intro k
    simp [scaled, integral_const_mul, H.centered]
  · have he : total (scaled A c X) = fun ω => c * V ω := funext (total_scaled A c)
    have hm : (∫ ω, V ω ∂μ) = 0 := by
      simp [V, outsideSum, integral_finset_sum A (fun k _ => (H.squareIntegrable k).integrable (by norm_num)),
        A, H.centered]
    have hV : AEMeasurable V μ := (memLp_finset_sum A (fun k _ => H.squareIntegrable k)).aemeasurable
    change variance (total (scaled A c X)) μ = 1
    rw [he, variance_mul, variance_of_integral_eq_zero hV hm, ← rms_sq]
    dsimp only [c]
    field_simp [show rms μ V ≠ 0 from hs.ne']

end JanischLehericy
