import TNumbersLean.HeightRangeCoverage

namespace TNumbersLean

/-- Only the external threshold data of Lemma 2.1 and the initial integer scale.
Thresholds below degree two are unused and unrestricted. -/
structure ScheduleThresholds where
  T : ℕ → ℕ
  monotone : MonotoneOn T (Set.Ici 2)
  threshold_ge_four : ∀ d, 2 ≤ d → 4 ≤ T d
  Q₁ : ℕ
  initial_threshold : T 2 ≤ Q₁

namespace ScheduleThresholds

variable (t : ScheduleThresholds)

/-- The finite set in (3.1). Pair index i is manuscript j=i+1. -/
def availableDegrees (i q : ℕ) : Finset ℕ :=
  (Finset.range (i + 3)).filter (fun d => 2 ≤ d ∧ t.T d ≤ q)

/-- Bounded search for the actual maximum in (3.1), without opaque choice. -/
def selectDegree (i q : ℕ) : ℕ :=
  Nat.findGreatest (fun d => 2 ≤ d ∧ t.T d ≤ q) (i + 2)

/-- Mathlib's natural 2-adic valuation, used only at positive pair numbers. -/
def v₂ (j : ℕ) : ℕ := padicValNat 2 j

/-- Integer scale at the beginning of pair i (manuscript Q_{2i+1}).
The two scale updates are exactly (3.3); thresholds cause no extra jump. -/
def pairScale : ℕ → ℕ
  | 0 => t.Q₁
  | i + 1 =>
    let D := t.selectDegree i (pairScale i)
    let q := pairScale i ^ (100 * stageExponent D)
    q ^ (100 * stageExponent (min D (2 + v₂ (i + 1))))

/-- Lean pair i is manuscript pair j=i+1. -/
def concreteD (i : ℕ) : ℕ := t.selectDegree i (t.pairScale i)

/-- Lean stage k is manuscript stage k+1: even k=2i is an odd paper stage. -/
def concreteDegree (k : ℕ) : ℕ :=
  if k % 2 = 0 then t.concreteD (k / 2)
  else min (t.concreteD (k / 2)) (2 + v₂ (k / 2 + 1))

def concreteExponent (k : ℕ) : ℕ := stageExponent (t.concreteDegree k)

/-- The full integer scale sequence, including the intermediate scale of a pair. -/
def concreteQ (k : ℕ) : ℕ :=
  if k % 2 = 0 then t.pairScale (k / 2)
  else t.pairScale (k / 2) ^ (100 * stageExponent (t.concreteD (k / 2)))

theorem availableDegrees_nonempty (i q : ℕ) (hq : t.T 2 ≤ q) :
    (t.availableDegrees i q).Nonempty := by
  refine ⟨2, ?_⟩
  simp [availableDegrees, hq]

theorem selectDegree_spec (i q : ℕ) (hq : t.T 2 ≤ q) :
    2 ≤ t.selectDegree i q ∧ t.selectDegree i q ≤ i + 2 ∧
      t.T (t.selectDegree i q) ≤ q := by
  have hs := Nat.findGreatest_spec (P := fun d => 2 ≤ d ∧ t.T d ≤ q)
    (show 2 ≤ i + 2 by omega) ⟨le_rfl, hq⟩
  exact ⟨hs.1, Nat.findGreatest_le _, hs.2⟩

theorem selectDegree_maximal (i q d : ℕ) (hd : 2 ≤ d) (hb : d ≤ i + 2)
    (hT : t.T d ≤ q) : d ≤ t.selectDegree i q :=
  Nat.le_findGreatest hb ⟨hd, hT⟩

theorem selectDegree_mem (i q : ℕ) (hq : t.T 2 ≤ q) :
    t.selectDegree i q ∈ t.availableDegrees i q := by
  have hs := t.selectDegree_spec i q hq
  simp only [availableDegrees, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hs.1, hs.2.2⟩

theorem selectDegree_greatest (i q d : ℕ) (hd : d ∈ t.availableDegrees i q) :
    d ≤ t.selectDegree i q := by
  simp only [availableDegrees, Finset.mem_filter, Finset.mem_range] at hd
  exact t.selectDegree_maximal i q d hd.2.1 (by omega) hd.2.2

theorem stageExponent_pos (d : ℕ) : 0 < stageExponent d := by
  unfold stageExponent
  positivity

theorem scale_update_ge (q d : ℕ) : q ≤ q ^ (100 * stageExponent d) := by
  exact Nat.le_self_pow (by have := stageExponent_pos d; omega) q

theorem pairScale_initial_le (i : ℕ) : t.Q₁ ≤ t.pairScale i := by
  induction i with
  | zero => rfl
  | succ i hi =>
    exact hi.trans ((scale_update_ge _ _).trans (scale_update_ge _ _))

theorem concreteD_spec (i : ℕ) :
    2 ≤ t.concreteD i ∧ t.concreteD i ≤ i + 2 ∧
      t.T (t.concreteD i) ≤ t.pairScale i :=
  t.selectDegree_spec i _ (t.initial_threshold.trans (t.pairScale_initial_le i))

theorem concreteD_maximal (i d : ℕ) (hd : 2 ≤ d) (hb : d ≤ i + 2)
    (hT : t.T d ≤ t.pairScale i) : d ≤ t.concreteD i :=
  t.selectDegree_maximal i _ d hd hb hT

/-- Nonemptiness at every actual pair, using the initial threshold and growth. -/
theorem concrete_availableDegrees_nonempty (i : ℕ) :
    (t.availableDegrees i (t.pairScale i)).Nonempty :=
  t.availableDegrees_nonempty i _
    (t.initial_threshold.trans (t.pairScale_initial_le i))

/-- The literal maximum of the finite set in (3.1) at every pair. -/
theorem concreteD_isGreatest (i : ℕ) :
    IsGreatest (t.availableDegrees i (t.pairScale i) : Set ℕ) (t.concreteD i) := by
  exact ⟨t.selectDegree_mem i _
    (t.initial_threshold.trans (t.pairScale_initial_le i)),
    fun _ hd => t.selectDegree_greatest i _ _ hd⟩

@[simp] theorem concreteDegree_even (i : ℕ) :
    t.concreteDegree (2 * i) = t.concreteD i := by
  simp [concreteDegree]

@[simp] theorem concreteDegree_odd (i : ℕ) :
    t.concreteDegree (2 * i + 1) = min (t.concreteD i) (2 + v₂ (i + 1)) := by
  simp [concreteDegree, Nat.add_div]

@[simp] theorem concreteQ_even (i : ℕ) : t.concreteQ (2 * i) = t.pairScale i := by
  simp [concreteQ]

@[simp] theorem concreteQ_odd (i : ℕ) :
    t.concreteQ (2 * i + 1) = t.pairScale i ^ (100 * stageExponent (t.concreteD i)) := by
  simp [concreteQ, Nat.add_div]

theorem concreteDegree_ge_two (k : ℕ) : 2 ≤ t.concreteDegree k := by
  unfold concreteDegree
  split
  · exact (t.concreteD_spec _).1
  · exact le_min (t.concreteD_spec _).1 (by omega)

theorem concreteDegree_le_pair (k : ℕ) : t.concreteDegree k ≤ k / 2 + 2 := by
  unfold concreteDegree
  split
  · exact (t.concreteD_spec _).2.1
  · exact (min_le_left _ _).trans (t.concreteD_spec _).2.1

theorem concreteExponent_bounds (k : ℕ) :
    27 ≤ t.concreteExponent k ∧ t.concreteExponent k ≤ (k + 4)^3 := by
  have hl := t.concreteDegree_ge_two k
  have hu := t.concreteDegree_le_pair k
  constructor
  · change (2 + 1)^3 ≤ (t.concreteDegree k + 1)^3
    gcongr
  · apply stageExponent_le_of_degree_le
    omega

theorem concreteQ_recurrence (k : ℕ) :
    t.concreteQ (k + 1) = t.concreteQ k ^ (100 * t.concreteExponent k) := by
  have hrem := Nat.mod_lt k (by omega : 0 < 2)
  have hdiv := Nat.mod_add_div k 2
  rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with he | ho
  · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i := ⟨k / 2, by omega⟩
    simp [concreteExponent]
  · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i + 1 := ⟨k / 2, by omega⟩
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega]
    simp only [concreteQ_even, concreteQ_odd, concreteExponent, concreteDegree_odd]
    rfl

theorem concreteQ_initial_le (k : ℕ) : t.Q₁ ≤ t.concreteQ k := by
  unfold concreteQ
  split
  · exact t.pairScale_initial_le _
  · exact (t.pairScale_initial_le _).trans (scale_update_ge _ _)

theorem concreteQ_ge_four (k : ℕ) : 4 ≤ t.concreteQ k :=
  ((t.threshold_ge_four 2 le_rfl).trans t.initial_threshold).trans (t.concreteQ_initial_le k)

theorem concreteQ_strictMono : StrictMono t.concreteQ := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [concreteQ_recurrence]
  have hA := (t.concreteExponent_bounds k).1
  calc
    t.concreteQ k = t.concreteQ k ^ 1 := (pow_one _).symm
    _ < t.concreteQ k ^ (100 * t.concreteExponent k) :=
      pow_lt_pow_right₀ (by have := t.concreteQ_ge_four k; omega) (by omega)

theorem concreteQ_growth (k : ℕ) : t.Q₁ ^ (2^k) ≤ t.concreteQ k := by
  induction k with
  | zero => simp [concreteQ, pairScale]
  | succ k hi =>
    rw [concreteQ_recurrence]
    have hA := (t.concreteExponent_bounds k).1
    calc
      t.Q₁ ^ (2^(k+1)) = (t.Q₁ ^ (2^k))^2 := by rw [pow_succ, pow_mul]
      _ ≤ t.concreteQ k ^ 2 := by gcongr
      _ ≤ t.concreteQ k ^ (100 * t.concreteExponent k) :=
        pow_le_pow_right₀ (by have := t.concreteQ_ge_four k; omega) (by omega)

theorem concreteQ_tends_to_infinity :
    Filter.Tendsto t.concreteQ Filter.atTop Filter.atTop :=
  t.concreteQ_strictMono.tendsto_atTop

theorem concreteQ_real_tends_to_infinity :
    Filter.Tendsto (fun k => (t.concreteQ k : ℝ)) Filter.atTop Filter.atTop :=
  tendsto_natCast_atTop_atTop.comp t.concreteQ_tends_to_infinity

theorem pairScale_tends_to_infinity :
    Filter.Tendsto t.pairScale Filter.atTop Filter.atTop := by
  have hidx : Filter.Tendsto (fun i : ℕ => 2 * i) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun i => by dsimp; omega) Filter.tendsto_id
  simpa only [Function.comp_def, concreteQ_even] using t.concreteQ_tends_to_infinity.comp hidx

theorem eventually_concreteD_ge (d : ℕ) (hd : 2 ≤ d) :
    ∀ᶠ i in Filter.atTop, d ≤ t.concreteD i := by
  filter_upwards [Filter.eventually_ge_atTop d,
    t.pairScale_tends_to_infinity.eventually (Filter.eventually_ge_atTop (t.T d))] with i hi hT
  exact t.concreteD_maximal i d hd (by omega) hT

theorem concreteD_tends_to_infinity :
    Filter.Tendsto t.concreteD Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro d
  exact (t.eventually_concreteD_ge (max 2 d) (le_max_left _ _)).mono
    (fun _ hi => (le_max_right _ _).trans hi)

theorem concrete_threshold (k : ℕ) : t.T (t.concreteDegree k) ≤ t.concreteQ k := by
  unfold concreteDegree concreteQ
  split
  · exact (t.concreteD_spec _).2.2
  · exact (t.monotone (le_min (t.concreteD_spec _).1 (by omega)) (t.concreteD_spec _).1
      (min_le_left _ _)).trans ((t.concreteD_spec _).2.2.trans (scale_update_ge _ _))

theorem v₂_nonneg (j : ℕ) : 0 ≤ v₂ j := Nat.zero_le _

theorem recurrentDegree_ge_two (j : ℕ) : 2 ≤ 2 + v₂ j := by omega

theorem v₂_witness (r m : ℕ) : v₂ (2^r * (2*m+1)) = r := by
  unfold v₂
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]
  have ho : ¬ 2 ∣ 2*m+1 := by omega
  rw [padicValNat.eq_zero_of_not_dvd ho, Nat.add_zero]

theorem v₂_fiber_infinite (r : ℕ) : {j : ℕ | 0 < j ∧ v₂ j = r}.Infinite := by
  have hf : Function.Injective (fun m : ℕ => 2^r * (2*m+1)) := by
    intro a b hab
    have hp : 0 < 2^r := by positivity
    nlinarith
  apply (Set.infinite_range_of_injective hf).mono
  rintro j ⟨m, rfl⟩
  exact ⟨by positivity, v₂_witness r m⟩

theorem concrete_recurrent (d : ℕ) (hd : 2 ≤ d) :
    {k | t.concreteDegree k = d}.Infinite := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (t.eventually_concreteD_ge d hd)
  have hj : {j : ℕ | 0 < j ∧ v₂ j = d-2}.Infinite := v₂_fiber_infinite _
  have htail : {j : ℕ | 0 < j ∧ v₂ j = d-2 ∧ N+1 ≤ j}.Infinite := by
    have hs := hj.diff (Set.finite_lt_nat (N+1))
    apply hs.mono
    intro j h
    exact ⟨h.1.1, h.1.2, by simpa using h.2⟩
  have hinj : Set.InjOn (fun j : ℕ => 2*j-1) {j : ℕ | 0 < j ∧ v₂ j = d-2 ∧ N+1 ≤ j} := by
    intro a ha b hb hab
    simp only [Set.mem_setOf_eq] at ha hb
    change 2*a-1 = 2*b-1 at hab
    omega
  apply (htail.image hinj).mono
  rintro k ⟨j, hj, rfl⟩
  change 0 < j ∧ v₂ j = d-2 ∧ N+1 ≤ j at hj
  change t.concreteDegree (2*j-1) = d
  rw [show 2*j-1 = 2*(j-1)+1 by omega, concreteDegree_odd,
    show j-1+1 = j by omega, hj.2.1]
  have hDj := hN (j-1) (by omega)
  rw [show 2+(d-2) = d by omega, min_eq_right hDj]

theorem eventual_odd_admissible (n : ℕ) :
    ∃ N, ∀ i ≥ N, DegreeAdmissible t.concreteDegree n (2*i) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (t.eventually_concreteD_ge (max 2 (n+1)) (le_max_left _ _))
  refine ⟨N, fun i hi => ?_⟩
  unfold DegreeAdmissible
  rw [concreteDegree_even]
  have := hN i hi
  have := le_max_right 2 (n+1)
  omega

theorem concrete_eventual_next_admissible (n : ℕ) (_hn : 1 ≤ n) :
    ∃ k₀, ∀ k ≥ k₀, DegreeAdmissible t.concreteDegree n (k+1) ∨
      DegreeAdmissible t.concreteDegree n (k+2) := by
  obtain ⟨N, hN⟩ := t.eventual_odd_admissible n
  refine ⟨2*N, fun k hk => ?_⟩
  have hrem := Nat.mod_lt k (by omega : 0 < 2)
  have hdiv := Nat.mod_add_div k 2
  by_cases he : k % 2 = 0
  · right
    rw [show k+2 = 2*(k/2+1) by omega]
    exact hN _ (by omega)
  · left
    rw [show k+1 = 2*(k/2+1) by omega]
    exact hN _ (by omega)

/-- Every field is proved from the recursive integer construction, not assumed. -/
def concreteCriterionSchedule : CriterionSchedule where
  Q k := (t.concreteQ k : ℝ)
  d := t.concreteDegree
  A := t.concreteExponent
  scale_ge_four k := by exact_mod_cast t.concreteQ_ge_four k
  degree_ge_two := t.concreteDegree_ge_two
  exponent_eq _ := rfl
  scale_recurrence k := by exact_mod_cast t.concreteQ_recurrence k
  scale_tends_to_infinity := t.concreteQ_real_tends_to_infinity
  recurrent := t.concrete_recurrent
  eventual_next_admissible := t.concrete_eventual_next_admissible

/-- The already certified (3.6) now applies to the constructed schedule. -/
theorem concrete_eventual_scale_gap (n : ℕ) (hn : 1 ≤ n) :
    ∃ N, ∀ k ≥ N, ∀ k',
      ConsecutiveAdmissible (DegreeAdmissible t.concreteDegree n) k k' →
        (k' = k+1 ∨ k' = k+2) ∧
        (t.concreteQ k' : ℝ) ≤ (t.concreteQ k : ℝ) ^
          (aCoeff (n : ℝ) * (t.concreteExponent k : ℝ)) :=
  t.concreteCriterionSchedule.exists_eventual_scale_gap n hn

/-- Lemma 3.1 for the literal recursively constructed schedule, with the paper's
stage k+1 represented by Lean k. The last conjunct is exactly (3.6). -/
theorem lemma_three_one :
    Filter.Tendsto t.concreteD Filter.atTop Filter.atTop ∧
    (∀ d, 2 ≤ d → {k | t.concreteDegree k = d}.Infinite) ∧
    (∀ k, t.T (t.concreteDegree k) ≤ t.concreteQ k ∧
      27 ≤ t.concreteExponent k ∧ t.concreteExponent k ≤ (k+4)^3 ∧
      t.Q₁ ^ (2^k) ≤ t.concreteQ k) ∧
    StrictMono t.concreteQ ∧
    Filter.Tendsto t.concreteQ Filter.atTop Filter.atTop ∧
    (∀ n, 1 ≤ n → ∃ N, ∀ k ≥ N, ∀ k',
      ConsecutiveAdmissible (DegreeAdmissible t.concreteDegree n) k k' →
        (k' = k+1 ∨ k' = k+2) ∧
        (t.concreteQ k' : ℝ) ≤ (t.concreteQ k : ℝ) ^
          (aCoeff (n : ℝ) * (t.concreteExponent k : ℝ))) := by
  refine ⟨t.concreteD_tends_to_infinity, t.concrete_recurrent, ?_,
    t.concreteQ_strictMono, t.concreteQ_tends_to_infinity, t.concrete_eventual_scale_gap⟩
  intro k
  exact ⟨t.concrete_threshold k, (t.concreteExponent_bounds k).1,
    (t.concreteExponent_bounds k).2, t.concreteQ_growth k⟩

end ScheduleThresholds
end TNumbersLean
