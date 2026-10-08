import Mathlib

namespace TNumbersLean

/-- The schedule coefficient (a_n=100^2(n+1)^3) from Proposition 3.2. -/
def scheduleCoeff (n : ℕ) : ℕ :=
  10000 * (n + 1)^3

/-- The manuscript exponent (A_k=(d_k+1)^3), isolated as a function of the degree. -/
def stageExponent (d : ℕ) : ℕ :=
  (d + 1)^3

/-- Two admissible stages are consecutive when there is no admissible stage strictly between them. -/
def ConsecutiveAdmissible (admissible : ℕ → Prop) (k k' : ℕ) : Prop :=
  admissible k ∧
  admissible k' ∧
  k < k' ∧
  ∀ m, k < m → m < k' → ¬ admissible m

/-- Abstract form of the bounded-gap step used in Lemma 3.1:
if one of the next two stages is admissible, then the next consecutive
admissible stage is at distance at most two. -/
theorem consecutive_admissible_gap_le_two
    (admissible : ℕ → Prop) (k k' : ℕ)
    (hcon : ConsecutiveAdmissible admissible k k')
    (hnext : admissible (k + 1) ∨ admissible (k + 2)) :
    k' ≤ k + 2 := by
  rcases hcon with ⟨hk, hk', hlt, hnone⟩
  by_contra h
  have hbig : k + 2 < k' := by
    omega
  rcases hnext with h1 | h2
  · exact (hnone (k + 1) (by omega) (by omega)) h1
  · exact (hnone (k + 2) (by omega) (by omega)) h2

/-- If two consecutive admissible stages are exactly two indices apart,
the intermediate stage is not admissible. -/
theorem skipped_stage_not_admissible
    (admissible : ℕ → Prop) (k : ℕ)
    (hcon : ConsecutiveAdmissible admissible k (k + 2)) :
    ¬ admissible (k + 1) := by
  rcases hcon with ⟨hk, hk2, hlt, hnone⟩
  exact hnone (k + 1) (by omega) (by omega)

/-- Admissibility for a fixed target degree (n): the stage degree exceeds (n). -/
def DegreeAdmissible (degrees : ℕ → ℕ) (n k : ℕ) : Prop :=
  n < degrees k

/-- In a two-step gap, the skipped stage has degree at most (n). -/
theorem skipped_degree_le
    (degrees : ℕ → ℕ) (n k : ℕ)
    (hcon :
      ConsecutiveAdmissible (DegreeAdmissible degrees n) k (k + 2)) :
    degrees (k + 1) ≤ n := by
  have hnot :=
    skipped_stage_not_admissible (DegreeAdmissible degrees n) k hcon
  unfold DegreeAdmissible at hnot
  omega

/-- Monotonicity of the cubic stage exponent. -/
theorem stageExponent_le_of_degree_le
    (d n : ℕ) (h : d ≤ n) :
    stageExponent d ≤ (n + 1)^3 := by
  unfold stageExponent
  gcongr

/-- Therefore the intermediate exponent in a two-step admissible gap
is bounded by ((n+1)^3), exactly as used before equation (3.6). -/
theorem skipped_stage_exponent_le
    (degrees : ℕ → ℕ) (n k : ℕ)
    (hcon :
      ConsecutiveAdmissible (DegreeAdmissible degrees n) k (k + 2)) :
    stageExponent (degrees (k + 1)) ≤ (n + 1)^3 := by
  exact stageExponent_le_of_degree_le _ _
    (skipped_degree_le degrees n k hcon)

/-- The exponent budget for a two-step gap:
(100^2 A_k A_{k+1}le a_n A_k) whenever (A_{k+1}le(n+1)^3). -/
theorem two_step_schedule_exponent_le
    (n A B : ℕ)
    (hB : B ≤ (n + 1)^3) :
    10000 * A * B ≤ scheduleCoeff n * A := by
  unfold scheduleCoeff
  have hmul : A * B ≤ A * (n + 1)^3 := by
    exact Nat.mul_le_mul_left A hB
  calc
    10000 * A * B = 10000 * (A * B) := by ring
    _ ≤ 10000 * (A * (n + 1)^3) := by
      exact Nat.mul_le_mul_left 10000 hmul
    _ = (10000 * (n + 1)^3) * A := by ring

/-- The one-step exponent (100A_k) is also bounded by (a_nA_k). -/
theorem one_step_schedule_exponent_le
    (n A : ℕ) :
    100 * A ≤ scheduleCoeff n * A := by
  have hpow : 1 ≤ (n + 1)^3 := by
    positivity
  have hcoeff : 100 ≤ scheduleCoeff n := by
    unfold scheduleCoeff
    nlinarith
  exact Nat.mul_le_mul_right A hcoeff

end TNumbersLean
