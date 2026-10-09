import TNumbersLean.ConcreteCriterionInputs

namespace TNumbersLean

/-- The literal stage information supplied by the support of a prime-denominator
Fourier packet in the manuscript.  Compared with `StageWitness`, primality
and nondivisibility are kept in their native form. -/
def PacketStageWitness
    (t : ScheduleThresholds) (x : ℝ) (k : ℕ) (p : ℤ) (q : ℕ) : Prop :=
  Nat.Prime q ∧
    ¬ q ∣ p.natAbs ∧
    t.concreteQ k ≤ q ∧
    q < 2 * t.concreteQ k ∧
    |x - theta (t.concreteDegree k) - (p : ℝ) / (q : ℝ)| ≤
      (1 / 4 : ℝ) * (q : ℝ) ^ (-(t.concreteExponent k : ℝ))

/-- A point selected by a prime-denominator packet supplies exactly the
reduced rational witness required by the arithmetic construction set. -/
theorem PacketStageWitness.toStageWitness
    {t : ScheduleThresholds} {x : ℝ} {k q : ℕ} {p : ℤ}
    (h : PacketStageWitness t x k p q) :
    StageWitness t x k p q := by
  rcases h with ⟨hqprime, hnotdiv, hqlo, hqhi, happ⟩
  refine ⟨hqprime.pos, ?_, hqlo, hqhi, happ⟩
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqprime).2 hnotdiv)

/-- Support information at every packet stage puts a point in the concrete
set E(J;Q₁) used by the already formalized T-number criterion. -/
theorem memE_of_packetStageWitness
    {t : ScheduleThresholds} {J : Set ℝ} {x : ℝ}
    (hxJ : x ∈ J)
    (hw : ∀ k, ∃ p : ℤ, ∃ q : ℕ, PacketStageWitness t x k p q) :
    MemE t J x := by
  refine ⟨hxJ, ?_⟩
  intro k
  obtain ⟨p, q, hpq⟩ := hw k
  exact ⟨p, q, hpq.toStageWitness⟩

end TNumbersLean
