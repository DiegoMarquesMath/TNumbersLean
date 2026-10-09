import Mathlib

namespace TNumbersLean

open Filter Asymptotics
open scoped Topology

/-- The model series used after the lacunary Fourier estimate:
    n exp(-c n^(1/4)). -/
noncomputable def stretchedExpMomentTerm (c : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.exp (-c * (n : ℝ) ^ ((1 : ℝ) / 4))

/-- The stretched-exponential model series from Section 6 is summable
for every positive decay constant. -/
theorem summable_stretchedExpMomentTerm {c : ℝ} (hc : 0 < c) :
    Summable (stretchedExpMomentTerm c) := by
  let p : ℝ := (1 : ℝ) / 4
  have hp : 0 < p := by
    dsimp [p]
    norm_num
  have hg :
      Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop atTop :=
    (Real.tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  have hexp :
      (fun n : ℕ => Real.exp (-c * (n : ℝ) ^ p)) =o[atTop]
        (fun n : ℕ => ((n : ℝ) ^ p) ^ (-12 : ℝ)) :=
    (Real.isLittleO_exp_neg_mul_rpow_atTop hc (-12 : ℝ)).comp_tendsto hg
  have hmul :
      (fun n : ℕ => (n : ℝ) * Real.exp (-c * (n : ℝ) ^ p)) =o[atTop]
        (fun n : ℕ => (n : ℝ) * (((n : ℝ) ^ p) ^ (-12 : ℝ))) :=
    (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO hexp
  have htarget (n : ℕ) :
      (n : ℝ) * (((n : ℝ) ^ p) ^ (-12 : ℝ)) =
        (n : ℝ) ^ (-2 : ℝ) := by
    by_cases hn : n = 0
    · subst n
      simp
    · have hnpos : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_mul hnpos.le p (-12 : ℝ)]
      rw [← Real.rpow_add hnpos]
      dsimp [p]
      norm_num
  have hsumTarget :
      Summable (fun n : ℕ => (n : ℝ) * (((n : ℝ) ^ p) ^ (-12 : ℝ))) := by
    refine (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).congr ?_
    intro n
    exact (htarget n).symm
  apply summable_of_isBigO_nat hsumTarget
  simpa [stretchedExpMomentTerm, p] using hmul.isBigO

end TNumbersLean
