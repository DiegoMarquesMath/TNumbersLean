import TNumbersLean.PrimePacket

namespace TNumbersLean

open Set
open scoped BigOperators

/-- Prime denominators in the manuscript dyadic window `[Q,2Q)`. -/
def packetPrimes (Q : ℕ) : Finset ℕ :=
  (Finset.Ico Q (2 * Q)).filter Nat.Prime

theorem mem_packetPrimes_iff {Q q : ℕ} :
    q ∈ packetPrimes Q ↔ Q ≤ q ∧ q < 2 * Q ∧ Nat.Prime q := by
  simp [packetPrimes, and_assoc, and_left_comm, and_comm]

/-- The packet `G_{Q,A,θ}`, defined as the normalized finite average of the
single-prime packets. -/
noncomputable def averagedPacket
    (φ : ℝ → ℝ) (Q A : ℕ) (θ₀ : ℝ) (x : ℝ) : ℝ :=
  (1 / (packetPrimes Q).card : ℝ) *
    ∑ q ∈ packetPrimes Q, primePacket φ q A θ₀ x

/-- Nonvanishing of the averaged packet forces nonvanishing of at least one
single-prime packet in the dyadic window. -/
theorem exists_primePacket_ne_zero_of_averagedPacket_ne_zero
    {φ : ℝ → ℝ} {Q A : ℕ} {θ₀ x : ℝ}
    (hx : averagedPacket φ Q A θ₀ x ≠ 0) :
    ∃ q ∈ packetPrimes Q, primePacket φ q A θ₀ x ≠ 0 := by
  have hsum :
      (∑ q ∈ packetPrimes Q, primePacket φ q A θ₀ x) ≠ 0 := by
    intro hz
    apply hx
    simp [averagedPacket, hz]
  by_contra h
  push_neg at h
  apply hsum
  apply Finset.sum_eq_zero
  intro q hq
  exact h q hq

/-- The geometric support property of the manuscript averaged packet. -/
theorem averagedPacket_ne_zero_implies_mem_primePacketSupport
    {φ : ℝ → ℝ}
    (hφ : Function.support φ ⊆ Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ))
    {Q A : ℕ} {θ₀ x : ℝ}
    (hx : averagedPacket φ Q A θ₀ x ≠ 0) :
    x ∈ primePacketSupport Q A θ₀ := by
  obtain ⟨q, hqmem, hqnonzero⟩ :=
    exists_primePacket_ne_zero_of_averagedPacket_ne_zero hx
  have hq := mem_packetPrimes_iff.mp hqmem
  exact mem_primePacketSupport_of_primePacket_ne_zero
    hφ hq.2.2 hq.1 hq.2.1 hqnonzero

/-- The averaged packet at stage `k` of the concrete schedule. -/
noncomputable def concreteStagePacket
    (φ : ℝ → ℝ) (t : ScheduleThresholds) (k : ℕ) (x : ℝ) : ℝ :=
  averagedPacket φ
    (t.concreteQ k)
    (t.concreteExponent k)
    (theta (t.concreteDegree k))
    x

theorem concreteStagePacket_ne_zero_implies_support
    {φ : ℝ → ℝ}
    (hφ : Function.support φ ⊆ Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ))
    {t : ScheduleThresholds} {k : ℕ} {x : ℝ}
    (hx : concreteStagePacket φ t k x ≠ 0) :
    x ∈ primePacketSupport
      (t.concreteQ k) (t.concreteExponent k) (theta (t.concreteDegree k)) := by
  exact averagedPacket_ne_zero_implies_mem_primePacketSupport hφ hx

end TNumbersLean
