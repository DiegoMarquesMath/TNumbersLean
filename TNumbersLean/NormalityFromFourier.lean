import Mathlib

namespace TNumbersLean

open Filter Finset MeasureTheory
open scoped BigOperators Topology

/-- The basic additive character used in the Weyl sums of Section 6. -/
noncomputable def circleExp (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * Complex.I)

/-- The summand exp(2π i h b^r x) from the manuscript. -/
noncomputable def weylTerm (b r : ℕ) (h : ℤ) (x : ℝ) : ℂ :=
  circleExp (2 * Real.pi * (h : ℝ) * (b : ℝ) ^ r * x)

/-- The manuscript sum S_N(x)=sum_{r=1}^N exp(2π i h b^r x). -/
noncomputable def weylSum (b : ℕ) (h : ℤ) (x : ℝ) (N : ℕ) : ℂ :=
  ∑ r ∈ Finset.range N, weylTerm b (r + 1) h x

/-- The normalized Weyl sum. -/
noncomputable def normalizedWeylSum (b : ℕ) (h : ℤ) (x : ℝ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * weylSum b h x N

@[simp]
theorem norm_circleExp (t : ℝ) : ‖circleExp t‖ = 1 := by
  simp [circleExp, Complex.norm_exp_ofReal_mul_I]

@[simp]
theorem norm_weylTerm (b r : ℕ) (h : ℤ) (x : ℝ) :
    ‖weylTerm b r h x‖ = 1 := by
  simp [weylTerm]

/-- A Weyl sum has the trivial bound |S_N| <= N. -/
theorem norm_weylSum_le (b : ℕ) (h : ℤ) (x : ℝ) (N : ℕ) :
    ‖weylSum b h x N‖ ≤ N := by
  rw [weylSum]
  calc
    ‖∑ r ∈ Finset.range N, weylTerm b (r + 1) h x‖
        ≤ ∑ r ∈ Finset.range N, ‖weylTerm b (r + 1) h x‖ := norm_sum_le _ _
    _ = N := by simp

/-- The tail between two Weyl sums is bounded by the number of added terms. -/
theorem norm_weylSum_sub_le (b : ℕ) (h : ℤ) (x : ℝ) {M N : ℕ} (hMN : M ≤ N) :
    ‖weylSum b h x N - weylSum b h x M‖ ≤ N - M := by
  rw [weylSum, weylSum, ← Finset.sum_Ico_eq_sub _ hMN]
  calc
    ‖∑ r ∈ Finset.Ico M N, weylTerm b (r + 1) h x‖
        ≤ ∑ r ∈ Finset.Ico M N, ‖weylTerm b (r + 1) h x‖ := norm_sum_le _ _
    _ = N - M := by
      simp [Nat.cast_sub hMN]

/-- The elementary square-subsequence gap used in the manuscript:
if j^2 <= N < (j+1)^2, then at most 2j+1 terms are missing. -/
theorem square_gap_le (j N : ℕ) (hlo : j ^ 2 ≤ N) (hhi : N < (j + 1) ^ 2) :
    N - j ^ 2 ≤ 2 * j + 1 := by
  have hs : (j + 1) ^ 2 = j ^ 2 + (2 * j + 1) := by ring
  rw [hs] at hhi
  omega

/-- The manuscript's interpolation estimate between consecutive square indices. -/
theorem norm_weylSum_between_squares
    (b : ℕ) (h : ℤ) (x : ℝ) {j N : ℕ}
    (hlo : j ^ 2 ≤ N) (hhi : N < (j + 1) ^ 2)
    {ε : ℝ} (hsq : ‖weylSum b h x (j ^ 2)‖ ≤ ε * (j : ℝ) ^ 2) :
    ‖weylSum b h x N‖ ≤
      ((2 * j + 1 : ℕ) : ℝ) + ε * (j : ℝ) ^ 2 := by
  have htail :
      ‖weylSum b h x N - weylSum b h x (j ^ 2)‖ ≤
        (N : ℝ) - ((j ^ 2 : ℕ) : ℝ) :=
    norm_weylSum_sub_le b h x hlo
  have hgap' :
      ((N - j ^ 2 : ℕ) : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
    exact_mod_cast square_gap_le j N hlo hhi
  rw [Nat.cast_sub hlo] at hgap'
  have hgap :
      (N : ℝ) - ((j ^ 2 : ℕ) : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) :=
    hgap'
  calc
    ‖weylSum b h x N‖ =
        ‖(weylSum b h x N - weylSum b h x (j ^ 2)) +
          weylSum b h x (j ^ 2)‖ := by
            rw [sub_add_cancel]
    _ ≤ ‖weylSum b h x N - weylSum b h x (j ^ 2)‖ +
          ‖weylSum b h x (j ^ 2)‖ := norm_add_le _ _
    _ ≤ ((N : ℝ) - ((j ^ 2 : ℕ) : ℝ)) + ε * (j : ℝ) ^ 2 :=
      add_le_add htail hsq
    _ ≤ ((2 * j + 1 : ℕ) : ℝ) + ε * (j : ℝ) ^ 2 :=
      add_le_add_right hgap _

/-- Every index lies between the square of its natural square root and
the next square. -/
theorem nat_sqrt_square_bounds (N : ℕ) :
    (Nat.sqrt N) ^ 2 ≤ N ∧ N < (Nat.sqrt N + 1) ^ 2 :=
  ⟨Nat.sqrt_le' N, Nat.lt_succ_sqrt' N⟩

/-- The square-interpolation estimate with the canonical choice j = floor(sqrt N). -/
theorem norm_weylSum_sqrt_interpolation
    (b : ℕ) (h : ℤ) (x : ℝ) (N : ℕ) {ε : ℝ}
    (hsq :
      ‖weylSum b h x ((Nat.sqrt N) ^ 2)‖ ≤
        ε * (Nat.sqrt N : ℝ) ^ 2) :
    ‖weylSum b h x N‖ ≤
      ((2 * Nat.sqrt N + 1 : ℕ) : ℝ) +
        ε * (Nat.sqrt N : ℝ) ^ 2 := by
  exact norm_weylSum_between_squares b h x
    (nat_sqrt_square_bounds N).1 (nat_sqrt_square_bounds N).2 hsq

/-- Bad sets on the square subsequence in the Borel--Cantelli step. -/
def squareBadSet (S : ℕ → ℝ → ℂ) (ε : ℝ) (j : ℕ) : Set ℝ :=
  {x | ε * (j : ℝ) ^ 2 < ‖S (j ^ 2) x‖}

/-- The exact first Borel--Cantelli deduction used in the manuscript:
summability of the square-subsequence bad sets gives eventual pointwise control. -/
theorem ae_eventually_square_control
    {μ : Measure ℝ} {S : ℕ → ℝ → ℂ} {ε : ℝ}
    (hsum : (∑' j : ℕ, μ (squareBadSet S ε j)) ≠ ⊤) :
    ∀ᵐ x ∂μ, ∀ᶠ j : ℕ in atTop,
      ‖S (j ^ 2) x‖ ≤ ε * (j : ℝ) ^ 2 := by
  have hbc := MeasureTheory.ae_eventually_notMem hsum
  filter_upwards [hbc] with x hx
  filter_upwards [hx] with j hj
  exact not_lt.mp (by simpa [squareBadSet] using hj)

/-- Weyl's exponential-sum criterion, recorded as the analytic intermediate
property used before identifying it with digit normality. -/
def WeylNormalToBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ h : ℤ, h ≠ 0 →
    Tendsto (fun N : ℕ => normalizedWeylSum b h x N) atTop (𝓝 0)

/-- Simultaneous Weyl normality for every integer base b >= 2. -/
def WeylAbsolutelyNormal (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → WeylNormalToBase b x

theorem weylNormalToBase_of_all_frequencies
    {b : ℕ} {x : ℝ}
    (h : ∀ m : ℤ, m ≠ 0 →
      Tendsto (fun N : ℕ => normalizedWeylSum b m x N) atTop (𝓝 0)) :
    WeylNormalToBase b x :=
  h

theorem weylAbsolutelyNormal_of_all_bases
    {x : ℝ}
    (h : ∀ b : ℕ, 2 ≤ b → WeylNormalToBase b x) :
    WeylAbsolutelyNormal x :=
  h

end TNumbersLean
