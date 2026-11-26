import JanischLehericy.Pair
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace JanischLehericy

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
variable {m : ℕ} (G : Neighborhoods ι m)

/-- A joint random vector on a finite set of indices. -/
def block (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) : s → ℝ := fun i => X i ω

/-- Independence of all separated blocks. Since neighborhoods are closed, the
separation premise already rules out overlapping blocks. -/
def IsDependencyGraph (μ : Measure Ω) (X : ι → Ω → ℝ) : Prop :=
  ∀ s t : Finset ι, (∀ i ∈ s, ∀ j ∈ t, j ∉ G.near i) →
    IndepFun (block X s) (block X t) μ

def outside (i j : ι) := univ \ (G.near i ∪ G.near j)

def outsideSum (X : ι → Ω → ℝ) (i j : ι) (ω : Ω) := ∑ k ∈ outside G i j, X k ω

theorem outside_card_lt (i j : ι) : (outside G i j).card < Fintype.card ι := by
  rw [← Finset.card_univ]
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, ?_⟩
  intro h
  have hi : i ∈ outside G i j := h.symm ▸ mem_univ i
  simp [outside, G.self_mem i] at hi

theorem outside_card_deleted (i j : ι) : (G.near i ∪ G.near j).card ≤ 2*m :=
  (card_union_le _ _).trans (by linarith [G.card_le i, G.card_le j])

theorem pair_independent_outside {μ : Measure Ω} {X : ι → Ω → ℝ}
    (h : IsDependencyGraph G μ X) (i j : ι) :
    IndepFun (fun ω => (X i ω, X j ω)) (outsideSum G X i j) μ := by
  let s : Finset ι := {i,j}
  let t := outside G i j
  have hin (k) (hk : k ∈ s) (l) (hl : l ∈ t) : l ∉ G.near k := by
    have hsep : l ∉ G.near i ∧ l ∉ G.near j := by simpa [t, outside] using hl
    have hmem : k = i ∨ k = j := by simpa [s] using hk
    rcases hmem with rfl | rfl
    · exact hsep.1
    · exact hsep.2
  let getPair := fun (x : s → ℝ) => (x ⟨i, by simp [s]⟩, x ⟨j, by simp [s]⟩)
  let getSum := fun (x : t → ℝ) => ∑ k, x k
  have hp : Measurable getPair := by dsimp [getPair]; fun_prop
  have hs : Measurable getSum := by dsimp [getSum]; fun_prop
  have hcomp := (h s t hin).comp hp hs
  have heq : getSum ∘ block X t = outsideSum G X i j := by
    funext ω
    exact (Finset.sum_attach t (fun k => X k ω))
  rw [heq] at hcomp
  exact hcomp

/-- Product-law integration for a random interval radius and weight that depend
only on the pair. Stating it for nonnegative integrals avoids auxiliary
integrability assumptions on the test weight. -/
theorem weighted_random_interval {S : Type*} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → S} {V : Ω → ℝ}
    (hY : Measurable Y) (hV : Measurable V) (hi : IndepFun Y V μ)
    (g : S → ℝ≥0∞) (hg : Measurable g) (r : S → ℝ) (hr : Measurable r)
    (u : ℝ) :
    (∫⁻ ω, g (Y ω) * (if |V ω - u| ≤ r (Y ω) then 1 else 0) ∂μ) =
      ∫⁻ y, g y * (μ.map V) {x | |x-u| ≤ r y} ∂(μ.map Y) := by
  classical
  let f : S × ℝ → ℝ≥0∞ := fun p =>
    g p.1 * (if |p.2-u| ≤ r p.1 then 1 else 0)
  have hset : MeasurableSet {p : S × ℝ | |p.2-u| ≤ r p.1} :=
    measurableSet_le (by fun_prop) (hr.comp measurable_fst)
  have hf : Measurable f := (hg.comp measurable_fst).mul
    (Measurable.ite hset measurable_const measurable_const)
  have hp := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hV.aemeasurable).mp hi
  calc
    _ = ∫⁻ p, f p ∂(μ.map (fun ω => (Y ω,V ω))) :=
      (lintegral_map hf (hY.prodMk hV)).symm
    _ = ∫⁻ p, f p ∂((μ.map Y).prod (μ.map V)) := by rw [hp]
    _ = _ := by
      rw [lintegral_prod _ hf.aemeasurable]
      apply lintegral_congr
      intro y
      dsimp [f]
      have hy : MeasurableSet {x : ℝ | |x-u| ≤ r y} :=
        measurableSet_le (by fun_prop) measurable_const
      rw [lintegral_const_mul _ (Measurable.ite hy measurable_const measurable_const)]
      congr 1
      change (∫⁻ x, ({x : ℝ | |x-u| ≤ r y} : Set ℝ).indicator (fun _ => (1 : ℝ≥0∞)) x ∂(μ.map V)) = _
      simp [lintegral_indicator hy]

end JanischLehericy
