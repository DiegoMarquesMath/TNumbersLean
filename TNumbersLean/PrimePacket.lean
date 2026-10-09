import TNumbersLean.PacketBumpGeometry

namespace TNumbersLean

open Set
open scoped BigOperators

/-- The single-prime packet from the manuscript, before averaging over
primes in `[Q,2Q)`.  The factor is the normalization used in the paper. -/
noncomputable def primePacket
    (φ : ℝ → ℝ) (q A : ℕ) (θ₀ : ℝ) (x : ℝ) : ℝ :=
  ((q : ℝ) ^ A / ((q : ℝ) - 1)) *
    ∑' p : ℤ,
      if q ∣ p.natAbs then 0 else packetBumpTerm φ q A θ₀ p x

/-- If a single-prime packet is nonzero, then at least one admissible
numerator contributes a nonzero bump term. -/
theorem exists_nonzero_packetBumpTerm_of_primePacket_ne_zero
    {φ : ℝ → ℝ} {q A : ℕ} {θ₀ x : ℝ}
    (hx : primePacket φ q A θ₀ x ≠ 0) :
    ∃ p : ℤ, ¬ q ∣ p.natAbs ∧ packetBumpTerm φ q A θ₀ p x ≠ 0 := by
  have hsum :
      (∑' p : ℤ,
        if q ∣ p.natAbs then 0 else packetBumpTerm φ q A θ₀ p x) ≠ 0 := by
    intro hz
    apply hx
    simp [primePacket, hz]
  have hex :
      ∃ p : ℤ,
        (if q ∣ p.natAbs then 0 else packetBumpTerm φ q A θ₀ p x) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hsum
    simp [h]
  obtain ⟨p, hp⟩ := hex
  by_cases hdiv : q ∣ p.natAbs
  · simp [hdiv] at hp
  · refine ⟨p, hdiv, ?_⟩
    simpa [hdiv] using hp

/-- The analytic support statement for one prime packet. -/
theorem primePacket_ne_zero_implies_approx
    {φ : ℝ → ℝ}
    (hφ : Function.support φ ⊆ Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ))
    {q A : ℕ} (hq : 0 < q) {θ₀ x : ℝ}
    (hx : primePacket φ q A θ₀ x ≠ 0) :
    ∃ p : ℤ,
      ¬ q ∣ p.natAbs ∧
      |x - θ₀ - (p : ℝ) / (q : ℝ)| <
        (1 / 4 : ℝ) * (q : ℝ) ^ (-(A : ℝ)) := by
  obtain ⟨p, hpdiv, hp⟩ :=
    exists_nonzero_packetBumpTerm_of_primePacket_ne_zero hx
  exact ⟨p, hpdiv, packetBumpTerm_ne_zero_implies_approx hφ hq hp⟩

/-- For a prime denominator in the dyadic window, nonvanishing of the
single-prime packet places the point in the geometric packet support. -/
theorem mem_primePacketSupport_of_primePacket_ne_zero
    {φ : ℝ → ℝ}
    (hφ : Function.support φ ⊆ Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ))
    {Q q A : ℕ} {θ₀ x : ℝ}
    (hqprime : Nat.Prime q) (hqlo : Q ≤ q) (hqhi : q < 2 * Q)
    (hx : primePacket φ q A θ₀ x ≠ 0) :
    x ∈ primePacketSupport Q A θ₀ := by
  obtain ⟨p, hpdiv, happ⟩ :=
    primePacket_ne_zero_implies_approx hφ hqprime.pos hx
  exact ⟨p, q, hqprime, hpdiv, hqlo, hqhi, happ.le⟩

end TNumbersLean
