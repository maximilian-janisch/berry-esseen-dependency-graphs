import JanischLehericy.RawMoments

/-!
# Conjecture 1.4 of Janisch and Lehéricy

This is the statement of the 2024 journal paper (DOI 10.1007/s10959-024-01363-z).
The vertex type `ι` is finite and `μ` is a probability measure on `Ω`.
The hypothesis `hG` spells out graph dependence. For two disjoint sets of vertices
with no edge between them, the two joint random vectors are independent.

All notation on the right-hand side is defined in the theorem. The conclusion
bounds the difference of the two CDFs at every real threshold, hence their
Kolmogorov distance. The last line applies the proof in `RawMoments.lean`.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace JanischLehericy

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The published conjecture with one absolute constant for every `2 < δ ≤ 3`. -/
theorem conjecture_one_four (g : SimpleGraph ι) [DecidableRel g.Adj] (Y : ι → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i))
    (hG : ∀ A B : Finset ι, Disjoint A B →
      (∀ i ∈ A, ∀ j ∈ B, ¬ g.Adj i j) →
      IndepFun (fun ω (i : A) => Y i ω) (fun ω (j : B) => Y j ω) μ)
    {δ : ℝ} (h2 : 2 < δ) (h3 : δ ≤ 3)
    (hM : ∀ i, Integrable (fun ω => |Y i ω| ^ δ) μ)
    (hv : 0 < variance (fun ω => ∑ i, Y i ω) μ) :
    let S : Ω → ℝ := fun ω => ∑ i, Y i ω
    let v : ℝ := variance S μ
    let W : Ω → ℝ := fun ω => (S ω - ∫ t, S t ∂μ) / Real.sqrt v
    let N : ℝ := Fintype.card ι
    let m : ℝ := (g.maxDegree + 1 : ℕ)
    let Aδ : ℝ := ∑ i, ∫ ω, |Y i ω| ^ δ ∂μ
    let ξδ : ℝ := (N / Aδ) ^ (1 / δ) * Real.sqrt (v / (N * m))
    let Φ : ℝ → ℝ := cdf (gaussianReal 0 1)
    ∀ z : ℝ, |μ.real {ω | W ω ≤ z} - Φ z| ≤
      min 1 (2000000 * ξδ ^ (-δ) * (m / N) ^ ((δ - 2) / 2)) :=
  cdfBound_xi g Y hY hG h2 h3 hM hv

end JanischLehericy
