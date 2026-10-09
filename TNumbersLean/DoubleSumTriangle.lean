import Mathlib

namespace TNumbersLean

open Finset
open scoped BigOperators

/-- Generic triangular estimate for a finite double sum.  It is tailored to
the diagonal/off-diagonal decomposition in the Weyl second-moment argument:
the diagonal costs one per index, while an off-diagonal entry is controlled
by a weight attached to the larger index. -/
theorem double_sum_le_diag_add_two_triangle
    (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hdiag : ∀ r : ℕ, f r r ≤ 1)
    (hlower : ∀ {s r : ℕ}, s < r → f r s ≤ a r)
    (hupper : ∀ {r s : ℕ}, r < s → f r s ≤ a s) :
    ∀ N : ℕ,
      (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N, f r s)
        ≤ (N : ℝ) +
          2 * ∑ r ∈ Finset.range N, (r : ℝ) * a r := by
  intro N
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hup :
          (∑ r ∈ Finset.range N, f r N) ≤ (N : ℝ) * a N := by
        calc
          (∑ r ∈ Finset.range N, f r N)
              ≤ ∑ r ∈ Finset.range N, a N := by
                apply Finset.sum_le_sum
                intro r hr
                exact hupper (Finset.mem_range.mp hr)
          _ = (N : ℝ) * a N := by simp
      have hlo :
          (∑ s ∈ Finset.range N, f N s) ≤ (N : ℝ) * a N := by
        calc
          (∑ s ∈ Finset.range N, f N s)
              ≤ ∑ s ∈ Finset.range N, a N := by
                apply Finset.sum_le_sum
                intro s hs
                exact hlower (Finset.mem_range.mp hs)
          _ = (N : ℝ) * a N := by simp
      calc
        (∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1), f r s)
            =
          (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N, f r s) +
            (∑ r ∈ Finset.range N, f r N) +
            (∑ s ∈ Finset.range N, f N s) + f N N := by
              simp_rw [Finset.sum_range_succ]
              rw [Finset.sum_add_distrib]
              ring
        _ ≤
          ((N : ℝ) + 2 * ∑ r ∈ Finset.range N, (r : ℝ) * a r) +
            ((N : ℝ) * a N) + ((N : ℝ) * a N) + 1 := by
              gcongr
              exact hdiag N
        _ =
          ((N + 1 : ℕ) : ℝ) +
            2 * (∑ r ∈ Finset.range N, (r : ℝ) * a r +
              (N : ℝ) * a N) := by
              push_cast
              ring
        _ =
          ((N + 1 : ℕ) : ℝ) +
            2 * ∑ r ∈ Finset.range (N + 1), (r : ℝ) * a r := by
              rw [Finset.sum_range_succ]

end TNumbersLean
