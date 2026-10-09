import TNumbersLean.PerfectExtraction
import TNumbersLean.WeylAlmostEverywhere

namespace TNumbersLean

open MeasureTheory Set

/-- Final measure-theoretic assembly for the perfect-set part of Theorem 1.1.

If a positive-measure measurable set F carries the arithmetic property
constructed in the manuscript, then under the Fourier-decay hypothesis it
contains a nonempty compact perfect subset all of whose points satisfy the
simultaneous Weyl criterion for every integer base. -/
theorem exists_compact_perfect_weylAbsolutelyNormal_subset_of_pos_measure
    {μ : Measure ℝ} [IsProbabilityMeasure μ] [NoAtoms μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    {F : Set ℝ} (hF : MeasurableSet F) (hFpos : 0 < μ F) :
    ∃ P : Set ℝ,
      P.Nonempty ∧
      IsCompact P ∧
      Perfect P ∧
      P ⊆ F ∧
      ∀ x ∈ P, WeylAbsolutelyNormal x := by
  obtain ⟨G, hGae, hGmeas, hGnormal⟩ :=
    (ae_weylAbsolutelyNormal_of_fourierDecay hdecay).exists_measurable_mem
  have hGFpos : 0 < μ (G ∩ F) := by
    rw [Measure.measure_inter_eq_of_ae hGae]
    exact hFpos
  obtain ⟨P, hPnonempty, hPcompact, hPperfect, hPsubset⟩ :=
    exists_compact_perfect_subset_of_pos_measure
      (hGmeas.inter hF) hGFpos
  refine ⟨P, hPnonempty, hPcompact, hPperfect, ?_, ?_⟩
  · intro x hx
    exact (hPsubset hx).2
  · intro x hx
    exact hGnormal x (hPsubset hx).1

end TNumbersLean
