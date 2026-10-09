import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import TNumbersLean.AveragedPacket

namespace TNumbersLean

open scoped BigOperators

/-- Prime denominators in the dyadic packet window which divide `n`. -/
def packetPrimeDivisors (Q n : ℕ) : Finset ℕ :=
  (packetPrimes Q).filter fun q => q ∣ n

theorem mem_packetPrimeDivisors_iff {Q n q : ℕ} :
    q ∈ packetPrimeDivisors Q n ↔
      Q ≤ q ∧ q < 2 * Q ∧ Nat.Prime q ∧ q ∣ n := by
  simp [packetPrimeDivisors, mem_packetPrimes_iff, and_assoc]

/-- Every prime counted by the packet divisor set is a genuine prime factor of
`n`. -/
theorem packetPrimeDivisors_subset_primeFactors
    {Q n : ℕ} (hn : n ≠ 0) :
    packetPrimeDivisors Q n ⊆ n.primeFactors := by
  intro q hq
  rcases mem_packetPrimeDivisors_iff.mp hq with ⟨_, _, hprime, hdvd⟩
  exact Nat.Prime.mem_primeFactors hprime hdvd hn

/-- The squarefree product of all packet primes dividing `n` divides `n`. -/
theorem prod_packetPrimeDivisors_dvd
    {Q n : ℕ} (hn : n ≠ 0) :
    (∏ q ∈ packetPrimeDivisors Q n, q) ∣ n := by
  have hsub := packetPrimeDivisors_subset_primeFactors (Q := Q) hn
  have hprod :
      (∏ q ∈ packetPrimeDivisors Q n, q) ∣
        ∏ q ∈ n.primeFactors, q := by
    exact Finset.prod_dvd_prod_of_subset _ _ (fun q : ℕ => q) hsub
  exact hprod.trans (Nat.prod_primeFactors_dvd n)

/-- Since every packet denominator is at least `Q`, the number of packet
primes dividing a nonzero integer is bounded multiplicatively. -/
theorem pow_card_packetPrimeDivisors_le
    {Q n : ℕ} (hn : n ≠ 0) :
    Q ^ (packetPrimeDivisors Q n).card ≤ n := by
  have hlower :
      Q ^ (packetPrimeDivisors Q n).card ≤
        ∏ q ∈ packetPrimeDivisors Q n, q := by
    simpa using
      (Finset.pow_card_le_prod
        (packetPrimeDivisors Q n) id Q
        (fun q hq => (mem_packetPrimeDivisors_iff.mp hq).1))
  exact hlower.trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (prod_packetPrimeDivisors_dvd hn))

/-- Exact discrete logarithmic form of the manuscript divisor-count estimate.
This is the arithmetic core of
`# {q in P_Q : q | n} <= log n / log Q`. -/
theorem card_packetPrimeDivisors_le_natLog
    {Q n : ℕ} (hQ : 1 < Q) (hn : n ≠ 0) :
    (packetPrimeDivisors Q n).card ≤ Nat.log Q n := by
  exact Nat.le_log_of_pow_le hQ (pow_card_packetPrimeDivisors_le hn)

end TNumbersLean
