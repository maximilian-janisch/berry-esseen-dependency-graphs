import JanischLehericy.Restriction
import JanischLehericy.Comparison

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace JanischLehericy
universe u v

variable {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Stein smoothing estimate with a uniform bound on the expected pair error. -/
def SteinEstimate {ι : Type u} [Fintype ι] {m : ℕ} (G : Neighborhoods ι m)
    (μ : Measure Ω) (X : ι → Ω → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ K : ℝ, (∀ u, (∫ ω, pairError G μ X α u ω ∂μ) ≤ K) →
    CDFBound μ (total X) (2*α+6*K)

/-- Strong induction, including the induced dependency graphs, the changing
variance normalization, the independent random radius and the constants. -/
theorem truncated_of_stein
    (stein : ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] {m : ℕ} (G : Neighborhoods κ m)
      (X : κ → Ω → ℝ), 0 < m → NormalizedFamily G μ X → SteinEstimate G μ X)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {m : ℕ} (G : Neighborhoods ι m)
    (X : ι → Ω → ℝ) : TruncatedBound G μ X := by
  suffices main : ∀ n : ℕ, ∀ {κ : Type u} [Fintype κ] [DecidableEq κ] {d : ℕ}
      (G : Neighborhoods κ d) (X : κ → Ω → ℝ), Fintype.card κ = n → TruncatedBound G μ X by
    exact main _ G X rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro κ instK instD d graph Y hn hm H
    let B := beta μ d Y
    have hB : 0 < B := beta_pos hm H
    have hCDF := cdfBound_one (μ := μ) (total Y)
    intro z
    apply le_min (hCDF z)
    by_cases hsmall : B < 1/50000
    · let α := 50000*B
      have hα : 0 < α := mul_pos (by norm_num) hB
      have hα1 : α ≤ 1 := by dsimp [α]; linarith
      let η := 16*250000*B
      have hη : 0 ≤ η := by dsimp [η]; positivity
      have hwin i j u h (hh : 0 ≤ h) :
          μ.real {ω | |outsideSum graph Y i j ω-u| ≤ h} ≤ min 1 (2*h) + η := by
        let A := outside graph i j
        let V := outsideSum graph Y i j
        let σ := rms μ V
        have hs : 1/2 < σ := outside_rms_gt_half hm H hsmall i j
        have hs0 : 0 < σ := by linarith
        have hinv : σ⁻¹ ≤ 2 := by rw [inv_eq_one_div, div_le_iff₀ hs0]; linarith
        have hcard : Fintype.card A < n := by
          rw [Fintype.card_coe, ← hn]
          exact outside_card_lt graph i j
        have hN := normalized_outside H i j hs0
        have hd := ih _ hcard (induced graph A) (scaled A σ⁻¹ Y) rfl hm hN
        have he : total (scaled A σ⁻¹ Y) = fun ω => σ⁻¹ * V ω := funext (total_scaled A σ⁻¹)
        rw [he] at hd
        have hb := beta_scaled A hm (inv_nonneg.mpr hs0.le) hinv H.squareIntegrable
        have hd' : CDFBound μ (fun ω => σ⁻¹ * V ω) (8*250000*B) := by
          apply hd.mono
          apply (min_le_right _ _).trans
          calc
            _ ≤ 250000 * (8 * B) := mul_le_mul_of_nonneg_left hb (by norm_num)
            _ = _ := by ring
        have hV : Measurable V := Finset.measurable_sum _ (fun k _ => H.measurable k)
        have hh' := interval_of_cdf hV (inv_pos.mpr hs0) hinv (by positivity) hd' u h hh
        convert hh' using 1
        dsimp only [η]
        ring
      have hp := pairError_bound H hm hα hα1 hη hwin
      have hz := stein graph Y hm H α hα hα1 _ hp z
      apply absorption_constants B _ hB
      calc
        _ ≤ _ := hz
        _ = 2*(50000*B)+10752*B+24576*250000*B^2/(50000*B) := by
          dsimp only [α,η,B]
          ring
    · have hh : 1 ≤ 250000*B := by linarith
      exact (hCDF z).trans hh

end JanischLehericy
