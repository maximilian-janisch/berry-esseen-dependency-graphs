import Mathlib

open scoped BigOperators
open Finset

namespace JanischLehericy

/-- Closed neighborhoods. The degree bound counts the vertex itself. -/
structure Neighborhoods (ι : Type*) [Fintype ι] (m : ℕ) where
  near : ι → Finset ι
  self_mem : ∀ i, i ∈ near i
  symm_mem : ∀ i j, j ∈ near i ↔ i ∈ near j
  card_le : ∀ i, (near i).card ≤ m

variable {ι : Type*} [Fintype ι] {m : ℕ} (G : Neighborhoods ι m)

def pairs (f : ι → ι → ℝ) : ℝ := ∑ i, ∑ j ∈ G.near i, f i j

theorem pairs_swap (f : ι → ι → ℝ) :
    pairs G f = pairs G (fun i j => f j i) := by
  apply Finset.sum_comm'
  intro i j
  simpa using G.symm_mem i j

theorem pairs_le {f g : ι → ι → ℝ} (h : ∀ i j, j ∈ G.near i → f i j ≤ g i j) :
    pairs G f ≤ pairs G g := by
  exact sum_le_sum fun i _ => sum_le_sum (h i)

theorem pairs_add (f g : ι → ι → ℝ) :
    pairs G (fun i j => f i j + g i j) = pairs G f + pairs G g := by
  simp only [pairs, sum_add_distrib]

theorem pairs_mul (c : ℝ) (f : ι → ι → ℝ) :
    pairs G (fun i j => c * f i j) = c * pairs G f := by
  simp only [pairs, mul_sum]

theorem pairs_row_le (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    pairs G (fun i _ => f i) ≤ (m : ℝ) * ∑ i, f i := by
  unfold pairs
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  simpa [nsmul_eq_mul] using
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (G.card_le i) : ((G.near i).card : ℝ) ≤ m) (hf i)

def radius (a : ι → ℝ) (i : ι) := ∑ j ∈ G.near i, a j

def pairScale (m : ℕ) (a : ι → ℝ) (i j : ι) : ℝ := m * max (a i) (a j)

/-- Abstract version of the finite charging argument. On the retained pairs with
a controlled destination radius, the caller supplies the pointwise comparison. -/
theorem charge (hm : 0 < m) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : ℝ → ℝ) (hF : MonotoneOn F (Set.Ici 0)) (hF0 : ∀ s ≥ 0, 0 ≤ F s)
    (K : ι → ι → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hgood : ∀ i j, j ∈ G.near i → radius G a i ≤ 2 * m * a j →
      radius G a j ≤ 4 * pairScale m a i j → F (2 * radius G a i) ≤ K i j) :
    pairs G (fun i j => a i * a j * F (radius G a i + radius G a j)) ≤
      8 * pairs G (fun i j => a i * a j * K i j) := by
  let R := radius G a
  have hR (i) : 0 ≤ R i := sum_nonneg fun j _ => ha j
  let b := fun i j => a i * a j * F (2 * R i)
  let H := fun i => a i * R i * F (2 * R i)
  have hH (i) : 0 ≤ H i :=
    mul_nonneg (mul_nonneg (ha i) (hR i)) (hF0 (2 * R i) (by linarith [hR i]))
  have hrow : pairs G b = ∑ i, H i := by
    unfold pairs
    apply sum_congr rfl
    intro i _
    simp only [b, H, R, radius, mul_sum, sum_mul]
  have hfirst : pairs G (fun i j => a i * a j * F (R i + R j)) ≤
      pairs G (fun i j => b i j + b j i) := by
    apply pairs_le
    intro i j _
    have hbi : 0 ≤ b i j := mul_nonneg (mul_nonneg (ha i) (ha j)) (hF0 (2 * R i) (by linarith [hR i]))
    have hbj : 0 ≤ b j i := mul_nonneg (mul_nonneg (ha j) (ha i)) (hF0 _ (by linarith [hR j]))
    have hs : 0 ≤ R i + R j := add_nonneg (hR i) (hR j)
    rcases le_total (R j) (R i) with h | h
    · have hh := hF hs (by linarith [hR i] : 0 ≤ 2 * R i) (by linarith : R i + R j ≤ 2 * R i)
      exact le_trans (mul_le_mul_of_nonneg_left hh (mul_nonneg (ha i) (ha j))) (le_add_of_nonneg_right hbj)
    · have hh := hF hs (by linarith [hR j] : 0 ≤ 2 * R j) (by linarith : R i + R j ≤ 2 * R j)
      rw [mul_comm (a i) (a j)]
      exact le_trans (mul_le_mul_of_nonneg_left hh (mul_nonneg (ha j) (ha i))) (le_add_of_nonneg_left hbi)
  let k := fun i j => a i * a j * K i j
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hpoint : pairs G (fun i j => (4 * (m : ℝ)) * b i j) ≤
      pairs G (fun i j => (2 * H i + H j) + (4 * (m : ℝ)) * k i j) := by
    apply pairs_le
    intro i j hj
    have hk : 0 ≤ (4 * (m : ℝ)) * k i j :=
      mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (ha i) (ha j)) (hK i j))
    by_cases hret : R i ≤ 2 * (m : ℝ) * a j
    · by_cases hdest : R j ≤ 4 * pairScale m a i j
      · have h := mul_le_mul_of_nonneg_left (hgood i j hj hret hdest)
            (mul_nonneg (ha i) (ha j))
        have := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 4 * (m : ℝ))
        dsimp only [b, k] at *
        linarith [hH i, hH j]
      · have hi := mul_le_mul_of_nonneg_left (le_max_left (a i) (a j)) hm'.le
        have hj' := mul_le_mul_of_nonneg_left (le_max_right (a i) (a j)) hm'.le
        unfold pairScale at hdest
        have hsmall : 4 * (m : ℝ) * a i ≤ R j := by linarith
        have hinc : R i ≤ R j := by linarith [hR j]
        have hmono := hF (by linarith [hR i] : 0 ≤ 2 * R i)
            (by linarith [hR j] : 0 ≤ 2 * R j) (by linarith : 2 * R i ≤ 2 * R j)
        have hprod := mul_le_mul hsmall hmono (hF0 _ (by linarith [hR i])) (hR j)
        have h := mul_le_mul_of_nonneg_left hprod (ha j)
        have hscaled : (4 * (m : ℝ)) * b i j ≤ H j := by
          dsimp only [b, H]
          linarith only [h]
        linarith only [hscaled, hk, hH i]
    · have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_of_not_ge hret) (ha i))
          (hF0 (2 * R i) (by linarith [hR i]))
      have hscaled : 4 * (m : ℝ) * b i j ≤ 2 * H i := by
        dsimp only [b, H]
        linarith only [h]
      linarith only [hscaled, hH j, hk]
  have hr := pairs_row_le G H hH
  have hc : pairs G (fun _ j => H j) ≤ (m : ℝ) * ∑ i, H i := by
    rw [pairs_swap G (fun _ j => H j)]
    exact hr
  rw [pairs_mul, pairs_add, pairs_add, pairs_mul, pairs_mul, hrow] at hpoint
  have hfinal : (m : ℝ) * ∑ i, H i ≤ (m : ℝ) * (4 * pairs G k) := by
    linarith [hr, hc]
  have hfinal' := (le_of_mul_le_mul_left hfinal hm')
  rw [pairs_add, ← pairs_swap G b, hrow] at hfirst
  linarith only [hfirst, hfinal']

/-- The function controlling increments of the spatially smoothed Stein derivative. -/
noncomputable def rampBound (α w u s : ℝ) : ℝ :=
  if |w - u| ≤ α + s then min 1 (s / α) else 0

theorem rampBound_nonneg {α w u s : ℝ} (hα : 0 < α) (hs : 0 ≤ s) :
    0 ≤ rampBound α w u s := by
  unfold rampBound
  split_ifs <;> positivity

theorem rampBound_mono {α w u : ℝ} (hα : 0 < α) :
    MonotoneOn (rampBound α w u) (Set.Ici 0) := by
  intro s hs t ht h
  unfold rampBound
  change 0 ≤ s at hs
  change 0 ≤ t at ht
  split_ifs <;> first | exact min_le_min_left _ (div_le_div_of_nonneg_right h hα.le) | positivity | linarith

/-- The adjacent-pair inequality tests the sum outside both closed neighborhoods against an interval. -/
theorem adjacent_pair_inequality [DecidableEq ι] (hm : 0 < m)
    (v a : ι → ℝ) (ha : ∀ i, |v i| ≤ a i) (α wloc : ℝ) (hα : 0 < α) :
    pairs G (fun i j => a i * a j *
      rampBound α (∑ k, v k) wloc (radius G a i + radius G a j)) ≤
    8 * pairs G (fun i j =>
      a i * a j * (if |(∑ k ∈ univ \ (G.near i ∪ G.near j), v k) - wloc| ≤
        α + 10 * pairScale m a i j then min 1 (4 * pairScale m a i j / α) else 0)) := by
  classical
  have ha0 i := (abs_nonneg (v i)).trans (ha i)
  have hL i j : 0 ≤ pairScale m a i j := mul_nonneg (Nat.cast_nonneg _) (le_max_of_le_left (ha0 i))
  apply charge G hm a ha0 _ (rampBound_mono hα) (fun _ => rampBound_nonneg hα)
  · intro i j
    split_ifs <;> first | positivity | exact le_min zero_le_one (div_nonneg (by linarith [hL i j]) hα.le)
  · intro i j _ hi hj
    have hRi : radius G a i ≤ 2 * pairScale m a i j := by
      have h := mul_le_mul_of_nonneg_left (le_max_right (a i) (a j)) (Nat.cast_nonneg m : 0 ≤ (m : ℝ))
      unfold pairScale
      linarith
    have hdel : |∑ k ∈ G.near i ∪ G.near j, v k| ≤ radius G a i + radius G a j := by
      calc
        _ ≤ ∑ k ∈ G.near i ∪ G.near j, |v k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ G.near i ∪ G.near j, a k := sum_le_sum fun k _ => ha k
        _ ≤ _ := by
          have he := sum_union_inter (s₁ := G.near i) (s₂ := G.near j) (f := a)
          have hp : 0 ≤ ∑ k ∈ G.near i ∩ G.near j, a k := sum_nonneg fun k _ => ha0 k
          unfold radius
          linarith
    have htotal := sum_sdiff (subset_univ (G.near i ∪ G.near j)) (f := v)
    unfold rampBound
    split_ifs with hwin hout hout
    · exact min_le_min_left _ (div_le_div_of_nonneg_right (by linarith) hα.le)
    · exfalso
      apply hout
      calc
        _ = |((∑ k, v k) - wloc) - ∑ k ∈ G.near i ∪ G.near j, v k| := by congr 1; linarith
        _ ≤ _ := (abs_sub _ _).trans (by linarith only [hwin, hdel, hRi, hj])
    · exact le_min zero_le_one (div_nonneg (by linarith [hL i j]) hα.le)
    · exact le_rfl

end JanischLehericy
