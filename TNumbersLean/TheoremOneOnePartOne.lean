import TNumbersLean.ConcretePropositionThreeTwo
import TNumbersLean.PacketSupportSet
import TNumbersLean.TheoremOneOneAssembly

namespace TNumbersLean

open MeasureTheory Set

/-- Paper-facing assembly for Theorem 1.1(i).

Once the manuscript construction supplies an atomless probability measure with
the stated Fourier decay and positive mass on the concrete set E(J;Q₁), the
already verified arithmetic criterion and Fourier-normality mechanism produce
a nonempty compact perfect set contained in J whose points are simultaneously
T-numbers and Weyl-absolutely-normal. -/
theorem exists_compact_perfect_weylAbsolutelyNormal_TNumbers
    (t : ScheduleThresholds) (J : Set ℝ) (R : ℝ)
    (hR : 2 ≤ R) (hJ : J ⊆ Set.Ioo (-R) R)
    (H : SectionTwoInputs t R)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] [NoAtoms μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    (hEmeas : MeasurableSet {x : ℝ | MemE t J x})
    (hEpos : 0 < μ {x : ℝ | MemE t J x}) :
    ∃ P : Set ℝ,
      P.Nonempty ∧
      IsCompact P ∧
      Perfect P ∧
      P ⊆ J ∧
      (∀ x ∈ P, MemE t J x) ∧
      ∀ x ∈ P,
        realAlgebraicApproximationSystem.IsTNumber x ∧
        WeylAbsolutelyNormal x := by
  obtain ⟨P, hPnonempty, hPcompact, hPperfect, hPsubset, hPnormal⟩ :=
    exists_compact_perfect_weylAbsolutelyNormal_subset_of_pos_measure
      hdecay hEmeas hEpos
  refine ⟨P, hPnonempty, hPcompact, hPperfect, ?_, ?_, ?_⟩
  · intro x hx
    exact (hPsubset hx).1
  · intro x hx
    exact hPsubset hx
  · intro x hx
    have hE : MemE t J x := hPsubset hx
    exact ⟨concrete_isTNumber hR hJ hE H, hPnormal x hx⟩

/-- Construction-facing form of Theorem 1.1(i).

This version is tailored to the measure construction in the manuscript: it is
enough to produce a compact set K of positive measure, all of whose points
belong to E(J;Q₁).  In particular, no measurability statement for the full set
E(J;Q₁) is needed. -/
theorem exists_compact_perfect_weylAbsolutelyNormal_TNumbers_of_compact
    (t : ScheduleThresholds) (J : Set ℝ) (R : ℝ)
    (hR : 2 ≤ R) (hJ : J ⊆ Set.Ioo (-R) R)
    (H : SectionTwoInputs t R)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] [NoAtoms μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    {K : Set ℝ} (hKcompact : IsCompact K) (hKpos : 0 < μ K)
    (hKmemE : ∀ x ∈ K, MemE t J x) :
    ∃ P : Set ℝ,
      P.Nonempty ∧
      IsCompact P ∧
      Perfect P ∧
      P ⊆ K ∧
      P ⊆ J ∧
      ∀ x ∈ P,
        realAlgebraicApproximationSystem.IsTNumber x ∧
        WeylAbsolutelyNormal x := by
  obtain ⟨P, hPnonempty, hPcompact, hPperfect, hPsubset, hPnormal⟩ :=
    exists_compact_perfect_weylAbsolutelyNormal_subset_of_pos_measure
      hdecay hKcompact.measurableSet hKpos
  refine ⟨P, hPnonempty, hPcompact, hPperfect, hPsubset, ?_, ?_⟩
  · intro x hx
    exact (hKmemE x (hPsubset hx)).1
  · intro x hx
    have hE : MemE t J x := hKmemE x (hPsubset hx)
    exact ⟨concrete_isTNumber hR hJ hE H, hPnormal x hx⟩


/-- Geometric construction-facing form of Theorem 1.1(i).

It is enough for the limiting measure to give positive mass to a compact set
contained in the intersection of the prime-packet supports.  The conversion
from packet geometry to the arithmetic set `MemE` is automatic. -/
theorem exists_compact_perfect_weylAbsolutelyNormal_TNumbers_of_packetSupport
    (t : ScheduleThresholds) (J : Set ℝ) (R : ℝ)
    (hR : 2 ≤ R) (hJ : J ⊆ Set.Ioo (-R) R)
    (H : SectionTwoInputs t R)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] [NoAtoms μ]
    {C c : ℝ} (hdecay : HasPaperFourierDecay μ C c)
    {K : Set ℝ} (hKcompact : IsCompact K) (hKpos : 0 < μ K)
    (hKsupport : K ⊆ manuscriptPacketSet t J) :
    ∃ P : Set ℝ,
      P.Nonempty ∧
      IsCompact P ∧
      Perfect P ∧
      P ⊆ K ∧
      P ⊆ J ∧
      ∀ x ∈ P,
        realAlgebraicApproximationSystem.IsTNumber x ∧
        WeylAbsolutelyNormal x := by
  apply exists_compact_perfect_weylAbsolutelyNormal_TNumbers_of_compact
    t J R hR hJ H hdecay hKcompact hKpos
  intro x hx
  exact memE_of_mem_manuscriptPacketSet (hKsupport hx)

end TNumbersLean
