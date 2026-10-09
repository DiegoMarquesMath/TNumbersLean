import TNumbersLean.PacketSupport

namespace TNumbersLean

open Set

/-- The geometric support set of one prime-denominator packet.  It records only
the interval geometry used later in the arithmetic argument, independently of
the smooth bump used to build the density. -/
def primePacketSupport (Q A : ℕ) (θ₀ : ℝ) : Set ℝ :=
  {x : ℝ | ∃ p : ℤ, ∃ q : ℕ,
    Nat.Prime q ∧
    ¬ q ∣ p.natAbs ∧
    Q ≤ q ∧
    q < 2 * Q ∧
    |x - θ₀ - (p : ℝ) / (q : ℝ)| ≤
      (1 / 4 : ℝ) * (q : ℝ) ^ (-(A : ℝ))}

/-- At the concrete stage parameters, membership in the geometric packet
support is exactly existence of a `PacketStageWitness`. -/
theorem mem_primePacketSupport_iff_packetStageWitness
    {t : ScheduleThresholds} {x : ℝ} {k : ℕ} :
    x ∈ primePacketSupport
        (t.concreteQ k) (t.concreteExponent k) (theta (t.concreteDegree k)) ↔
      ∃ p : ℤ, ∃ q : ℕ, PacketStageWitness t x k p q := by
  rfl

/-- The Cantor-type geometric set forced by membership in every packet support.
This is the natural target for the support of the limiting measure. -/
def manuscriptPacketSet (t : ScheduleThresholds) (J : Set ℝ) : Set ℝ :=
  J ∩ ⋂ k : ℕ,
    primePacketSupport
      (t.concreteQ k) (t.concreteExponent k) (theta (t.concreteDegree k))

theorem manuscriptPacketSet_subset_J
    (t : ScheduleThresholds) (J : Set ℝ) :
    manuscriptPacketSet t J ⊆ J := by
  intro x hx
  exact hx.1

/-- The geometric packet support already contains all arithmetic information
needed by the previously formalized T-number criterion. -/
theorem memE_of_mem_manuscriptPacketSet
    {t : ScheduleThresholds} {J : Set ℝ} {x : ℝ}
    (hx : x ∈ manuscriptPacketSet t J) :
    MemE t J x := by
  apply memE_of_packetStageWitness hx.1
  intro k
  have hk :
      x ∈ primePacketSupport
        (t.concreteQ k) (t.concreteExponent k) (theta (t.concreteDegree k)) :=
    mem_iInter.mp hx.2 k
  exact mem_primePacketSupport_iff_packetStageWitness.mp hk

theorem manuscriptPacketSet_subset_memE
    (t : ScheduleThresholds) (J : Set ℝ) :
    manuscriptPacketSet t J ⊆ {x : ℝ | MemE t J x} := by
  intro x hx
  exact memE_of_mem_manuscriptPacketSet hx

end TNumbersLean
