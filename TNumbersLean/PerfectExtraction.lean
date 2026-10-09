import Mathlib

namespace TNumbersLean

open MeasureTheory Set

/-- Perfect-set extraction used in the proof of Theorem 1.1(i).

If an atomless finite Borel measure on `ℝ` gives positive mass to a
measurable set `F`, then `F` contains a nonempty compact perfect subset.
The proof uses inner regularity and the Cantor--Bendixson theorem already
available in mathlib. -/
theorem exists_compact_perfect_subset_of_pos_measure
    {μ : Measure ℝ} [IsFiniteMeasure μ] [NoAtoms μ]
    {F : Set ℝ} (hF : MeasurableSet F) (hpos : 0 < μ F) :
    ∃ P : Set ℝ, P.Nonempty ∧ IsCompact P ∧ Perfect P ∧ P ⊆ F := by
  have hfin : μ F ≠ ⊤ := measure_ne_top μ F
  obtain ⟨C, hCF, hCcompact, hCpos⟩ :
      ∃ C ⊆ F, IsCompact C ∧ 0 < μ C :=
    hF.exists_lt_isCompact_of_ne_top hfin hpos
  have hCuncountable : ¬ C.Countable := by
    intro hcount
    have hzero : μ C = 0 := hcount.measure_zero μ
    rw [hzero] at hCpos
    exact (lt_irrefl 0) hCpos
  obtain ⟨P, hPperfect, hPnonempty, hPC⟩ :
      ∃ P : Set ℝ, Perfect P ∧ P.Nonempty ∧ P ⊆ C :=
    exists_perfect_nonempty_of_isClosed_of_not_countable hCcompact.isClosed hCuncountable
  refine ⟨P, hPnonempty, ?_, hPperfect, hPC.trans hCF⟩
  exact IsCompact.of_isClosed_subset hCcompact hPperfect.closed hPC

end TNumbersLean
