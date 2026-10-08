import TNumbersLean.CriterionInputs

noncomputable section

namespace TNumbersLean
namespace CriterionSchedule

variable (s : CriterionSchedule)

/-- The usable exponent u_{k,n} in (3.13). -/
def usableExponent (n k : ℕ) : ℝ :=
  ((s.A k : ℝ) - K (n : ℝ) - 3) / ((n : ℝ) + 2)

/-- Left endpoint of the manuscript height interval (3.18). -/
def heightLeft (n k : ℕ) : ℝ := s.Q k ^ delta (n : ℝ)

/-- Right endpoint of the manuscript height interval (3.18). -/
def heightRight (n k : ℕ) : ℝ := s.Q k ^ s.usableExponent n k

/-- The existing real coefficient agrees with the schedule's natural coefficient. -/
theorem scheduleCoeff_cast (n : ℕ) : (scheduleCoeff n : ℝ) = aCoeff (n : ℝ) := by
  simp [scheduleCoeff, aCoeff]

/-- The existing delta is exactly 1/(4 a_n (n+2)), as in (3.16). -/
theorem height_delta_eq (n : ℕ) :
    delta (n : ℝ) = 1 / (4 * aCoeff (n : ℝ) * ((n : ℝ) + 2)) := by
  unfold delta aCoeff
  congr 1
  ring

theorem height_delta_pos (n : ℕ) : 0 < delta (n : ℝ) := by
  unfold delta
  positivity

theorem scale_pos (k : ℕ) : 0 < s.Q k := by
  linarith [s.scale_ge_four k]

theorem scale_ge_one (k : ℕ) : 1 ≤ s.Q k := by
  linarith [s.scale_ge_four k]

/-- The manuscript scales strictly increase; this is derived from recurrence. -/
theorem scale_strictMono : StrictMono s.Q := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hA : 0 < s.A k := by
    rw [s.exponent_eq]
    unfold stageExponent
    positivity
  calc
    s.Q k = s.Q k ^ (1 : ℕ) := (pow_one _).symm
    _ < s.Q k ^ (100 * s.A k) :=
      pow_lt_pow_right₀ (by linarith [s.scale_ge_four k]) (by omega)
    _ = s.Q (k + 1) := (s.scale_recurrence k).symm

/-- Positive delta makes the left endpoints strictly increase. -/
theorem heightLeft_strictMono (n : ℕ) : StrictMono (s.heightLeft n) := by
  intro k k' hkk'
  exact Real.rpow_lt_rpow (s.scale_pos k).le (s.scale_strictMono hkk') (height_delta_pos n)

/-- Positivity in (3.15), obtained from the existing cubic reserve. -/
theorem usableExponent_pos (n k : ℕ) (hk : DegreeAdmissible s.d n k) :
    0 < s.usableExponent n k := by
  have hA := CriterionInputs.admissible_exponent_lower (s := s) n k hk
  have hApos : 0 < (s.A k : ℝ) := by
    have hp : 0 < (n + 2)^3 := by positivity
    exact_mod_cast (lt_of_lt_of_le hp hA)
  have hl := TNumbersLean.usable_exponent_lower (n : ℝ) (s.A k : ℝ)
    (by positivity) (by exact_mod_cast hA)
  exact (div_pos hApos (by positivity)).trans_le hl

/-- Explicit two-step iteration of the scale recurrence. -/
theorem scale_two_step (k : ℕ) :
    s.Q (k + 2) = s.Q k ^ (10000 * s.A k * s.A (k + 1)) := by
  calc
    s.Q (k + 2) = s.Q (k + 1) ^ (100 * s.A (k + 1)) := by
      simpa [Nat.add_assoc] using s.scale_recurrence (k + 1)
    _ = s.Q k ^ (10000 * s.A k * s.A (k + 1)) := by
      rw [s.scale_recurrence k, ← pow_mul]
      congr 1
      ring

/-- The next consecutive admissible index is one or two stages later. -/
theorem consecutive_stage_cases (n k k' : ℕ)
    (hc : ConsecutiveAdmissible (DegreeAdmissible s.d n) k k')
    (hnext : DegreeAdmissible s.d n (k + 1) ∨ DegreeAdmissible s.d n (k + 2)) :
    k' = k + 1 ∨ k' = k + 2 := by
  have hgap := consecutive_admissible_gap_le_two _ k k' hc hnext
  have hlt := hc.2.2.1
  omega

/-- (3.6), first with natural powers, using the skipped degree in a two-step gap. -/
theorem consecutive_scale_gap_nat (n k k' : ℕ)
    (hc : ConsecutiveAdmissible (DegreeAdmissible s.d n) k k')
    (hnext : DegreeAdmissible s.d n (k + 1) ∨ DegreeAdmissible s.d n (k + 2)) :
    s.Q k' ≤ s.Q k ^ (scheduleCoeff n * s.A k) := by
  rcases s.consecutive_stage_cases n k k' hc hnext with rfl | rfl
  · rw [s.scale_recurrence k]
    exact pow_le_pow_right₀ (s.scale_ge_one k) (one_step_schedule_exponent_le n (s.A k))
  · rw [s.scale_two_step k]
    have hdegree := skipped_degree_le s.d n k hc
    have hA : s.A (k + 1) ≤ (n + 1)^3 := by
      rw [s.exponent_eq]
      exact stageExponent_le_of_degree_le _ _ hdegree
    exact pow_le_pow_right₀ (s.scale_ge_one k)
      (two_step_schedule_exponent_le n (s.A k) (s.A (k + 1)) hA)

/-- Conversion of the natural power in (3.6) to the paper's real exponent. -/
theorem scale_gap_power_eq (n k : ℕ) :
    s.Q k ^ (scheduleCoeff n * s.A k) =
      s.Q k ^ (aCoeff (n : ℝ) * (s.A k : ℝ)) := by
  rw [← Real.rpow_natCast, Nat.cast_mul, scheduleCoeff_cast]

/-- Full eventual form of (3.6), derived from the schedule fields. -/
theorem exists_eventual_scale_gap (n : ℕ) (hn : 1 ≤ n) :
    ∃ k₀, ∀ k ≥ k₀, ∀ k',
      ConsecutiveAdmissible (DegreeAdmissible s.d n) k k' →
      (k' = k + 1 ∨ k' = k + 2) ∧
      s.Q k' ≤ s.Q k ^ (aCoeff (n : ℝ) * (s.A k : ℝ)) := by
  obtain ⟨k₀, hnext⟩ := s.eventual_next_admissible n hn
  refine ⟨k₀, fun k hk k' hc => ⟨s.consecutive_stage_cases n k k' hc (hnext k hk), ?_⟩⟩
  rw [← s.scale_gap_power_eq n k]
  exact s.consecutive_scale_gap_nat n k k' hc (hnext k hk)

/-- Both inequalities in (3.17), with the scale bound supplied by (3.6). -/
theorem height_overlap_of_scale_gap (n k k' : ℕ)
    (hk : DegreeAdmissible s.d n k)
    (hgap : s.Q k' ≤ s.Q k ^ (aCoeff (n : ℝ) * (s.A k : ℝ))) :
    s.heightLeft n k' ≤ s.Q k ^ ((s.A k : ℝ) / (4 * ((n : ℝ) + 2))) ∧
      s.Q k ^ ((s.A k : ℝ) / (4 * ((n : ℝ) + 2))) ≤ s.heightRight n k := by
  have hA := CriterionInputs.admissible_exponent_lower (s := s) n k hk
  constructor
  · unfold heightLeft
    calc
      s.Q k' ^ delta (n : ℝ) ≤
          (s.Q k ^ (aCoeff (n : ℝ) * (s.A k : ℝ))) ^ delta (n : ℝ) :=
        Real.rpow_le_rpow (s.scale_pos k').le hgap (height_delta_pos n).le
      _ = s.Q k ^ ((s.A k : ℝ) / (4 * ((n : ℝ) + 2))) := by
        rw [← Real.rpow_mul (s.scale_pos k).le,
          overlap_exponent_identity (n : ℝ) (s.A k : ℝ) (by positivity)]
  · unfold heightRight usableExponent
    apply Real.rpow_le_rpow_of_exponent_le (s.scale_ge_one k)
    have hb := overlap_budget (n : ℝ) (s.A k : ℝ) (by positivity)
      (by exact_mod_cast hA)
    rwa [overlap_exponent_identity (n : ℝ) (s.A k : ℝ) (by positivity)] at hb

/-- Consecutive sufficiently late admissible height intervals overlap. -/
theorem exists_eventual_height_overlap (n : ℕ) (hn : 1 ≤ n) :
    ∃ k₀, ∀ k ≥ k₀, ∀ k',
      ConsecutiveAdmissible (DegreeAdmissible s.d n) k k' →
      s.heightLeft n k' ≤ s.heightRight n k := by
  obtain ⟨k₀, hgap⟩ := s.exists_eventual_scale_gap n hn
  refine ⟨k₀, fun k hk k' hc => ?_⟩
  have ho := s.height_overlap_of_scale_gap n k k' hc.1 (hgap k hk k' hc).2
  exact ho.1.trans ho.2

/-- Recurrent exact degree n+1 is a subset of the admissible stages. -/
theorem admissible_infinite (n : ℕ) (hn : 1 ≤ n) :
    {k | DegreeAdmissible s.d n k}.Infinite := by
  apply (s.recurrent (n + 1) (by omega)).mono
  intro k hk
  change s.d k = n + 1 at hk
  change n < s.d k
  rw [hk]
  exact Nat.lt_succ_self n

/-- Admissible stages occur beyond every prescribed index. -/
theorem exists_admissible_ge (n : ℕ) (hn : 1 ≤ n) (N : ℕ) :
    ∃ k ≥ N, DegreeAdmissible s.d n k := by
  obtain ⟨k, hk, hNk⟩ := (s.admissible_infinite n hn).exists_gt N
  exact ⟨k, hNk.le, hk⟩

/-- Positive real powers preserve divergence of the scales. -/
theorem heightLeft_tends_to_infinity (n : ℕ) :
    Filter.Tendsto (s.heightLeft n) Filter.atTop Filter.atTop :=
  (tendsto_rpow_atTop (height_delta_pos n)).comp s.scale_tends_to_infinity

/-- Every real height is eventually strictly below every left endpoint. -/
theorem eventually_heightLeft_gt (n : ℕ) (H : ℝ) :
    ∃ N, ∀ k ≥ N, H < s.heightLeft n k := by
  exact Filter.eventually_atTop.mp
    ((s.heightLeft_tends_to_infinity n).eventually (Filter.eventually_gt_atTop H))

/-- Divergence combined with recurrence gives large admissible left endpoints. -/
theorem exists_admissible_heightLeft_gt (n : ℕ) (hn : 1 ≤ n) (N : ℕ) (H : ℝ) :
    ∃ k ≥ N, DegreeAdmissible s.d n k ∧ H < s.heightLeft n k := by
  obtain ⟨M, hM⟩ := s.eventually_heightLeft_gt n H
  obtain ⟨k, hk, ha⟩ := s.exists_admissible_ge n hn (max N M)
  exact ⟨k, (le_max_left N M).trans hk, ha, hM k ((le_max_right N M).trans hk)⟩

/-- The last late admissible stage below H and its next admissible stage exist.
The proof bounds the eligible indices using divergence, takes their greatest
index, then takes the least admissible index above it. No monotonicity is used. -/
theorem exists_last_admissible_pair (n : ℕ) (hn : 1 ≤ n) (k₀ : ℕ)
    (ha₀ : DegreeAdmissible s.d n k₀) (H : ℝ) (hH : s.heightLeft n k₀ ≤ H) :
    ∃ k k', k₀ ≤ k ∧
      ConsecutiveAdmissible (DegreeAdmissible s.d n) k k' ∧
      s.heightLeft n k ≤ H ∧ H < s.heightLeft n k' := by
  classical
  obtain ⟨M, hM⟩ := s.eventually_heightLeft_gt n H
  let P : ℕ → Prop := fun k => k₀ ≤ k ∧ DegreeAdmissible s.d n k ∧ s.heightLeft n k ≤ H
  let bound := max M k₀
  let k := Nat.findGreatest P bound
  have hPk : P k := Nat.findGreatest_spec (le_max_right M k₀) ⟨le_rfl, ha₀, hH⟩
  have hlast : ∀ m, k < m → ¬ P m := by
    intro m hkm hm
    by_cases hmb : m ≤ bound
    · have hmk : m ≤ k := Nat.le_findGreatest hmb hm
      omega
    · have hMm : M ≤ m := by
        have hMb : M ≤ bound := le_max_left M k₀
        omega
      exact (not_lt_of_ge hm.2.2) (hM m hMm)
  have hex : ∃ m, k < m ∧ DegreeAdmissible s.d n m := by
    obtain ⟨m, hm, ha⟩ := s.exists_admissible_ge n hn (k + 1)
    exact ⟨m, by omega, ha⟩
  let k' := Nat.find hex
  have hk' : k < k' ∧ DegreeAdmissible s.d n k' := Nat.find_spec hex
  have hc : ConsecutiveAdmissible (DegreeAdmissible s.d n) k k' := by
    refine ⟨hPk.2.1, hk'.2, hk'.1, ?_⟩
    intro m hkm hmk' ham
    exact Nat.find_min hex hmk' ⟨hkm, ham⟩
  refine ⟨k, k', hPk.1, hc, hPk.2.2, ?_⟩
  apply lt_of_not_ge
  intro hle
  exact hlast k' hk'.1 ⟨by omega, hk'.2, hle⟩

/-- Global coverage (3.18), after any prescribed stage threshold. The covering
stage is explicitly late; H is any real height above the returned H₀. -/
theorem exists_height_cover (n : ℕ) (hn : 1 ≤ n) (N : ℕ) :
    ∃ H₀ : ℝ, 2 ≤ H₀ ∧ ∀ H ≥ H₀,
      ∃ k, N ≤ k ∧ DegreeAdmissible s.d n k ∧
        s.heightLeft n k ≤ H ∧ H ≤ s.heightRight n k := by
  obtain ⟨M, ho⟩ := s.exists_eventual_height_overlap n hn
  obtain ⟨k₀, hk₀, ha₀⟩ := s.exists_admissible_ge n hn (max N M)
  refine ⟨max 2 (s.heightLeft n k₀), le_max_left _ _, ?_⟩
  intro H hH
  have hleft₀ : s.heightLeft n k₀ ≤ H := (le_max_right _ _).trans hH
  obtain ⟨k, k', hk, hc, hleft, hnext⟩ :=
    s.exists_last_admissible_pair n hn k₀ ha₀ H hleft₀
  have hNk : N ≤ k := (le_max_left N M).trans (hk₀.trans hk)
  have hMk : M ≤ k := (le_max_right N M).trans (hk₀.trans hk)
  have hrange := height_in_current_range hleft hnext (ho k hMk k' hc)
  exact ⟨k, hNk, hc.1, hrange⟩

end CriterionSchedule
end TNumbersLean
