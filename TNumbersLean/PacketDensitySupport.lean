import TNumbersLean.AveragedPacket

namespace TNumbersLean

open Set

/-- The finite-stage densities `f_n` from the manuscript, with stage `k`
multiplying by the concrete averaged packet `G_k`. -/
noncomputable def packetDensity
    (φ f₀ : ℝ → ℝ) (t : ScheduleThresholds) : ℕ → ℝ → ℝ
  | 0 => f₀
  | n + 1 => fun x =>
      packetDensity φ f₀ t n x * concreteStagePacket φ t n x

@[simp]
theorem packetDensity_zero
    (φ f₀ : ℝ → ℝ) (t : ScheduleThresholds) :
    packetDensity φ f₀ t 0 = f₀ := rfl

@[simp]
theorem packetDensity_succ
    (φ f₀ : ℝ → ℝ) (t : ScheduleThresholds) (n : ℕ) (x : ℝ) :
    packetDensity φ f₀ t (n + 1) x =
      packetDensity φ f₀ t n x * concreteStagePacket φ t n x := rfl

/-- The finite intersection of packet supports forced after `n` stages. -/
def finitePacketSet
    (t : ScheduleThresholds) (J : Set ℝ) (n : ℕ) : Set ℝ :=
  {x : ℝ |
    x ∈ J ∧
    ∀ k < n,
      x ∈ primePacketSupport
        (t.concreteQ k) (t.concreteExponent k) (theta (t.concreteDegree k))}

theorem finitePacketSet_zero
    (t : ScheduleThresholds) (J : Set ℝ) :
    finitePacketSet t J 0 = J := by
  ext x
  simp [finitePacketSet]

/-- Nonvanishing of the finite-stage density forces all packet support
conditions already imposed, together with the original localization in `J`. -/
theorem packetDensity_ne_zero_implies_mem_finitePacketSet
    {φ f₀ : ℝ → ℝ}
    (hφ : Function.support φ ⊆ Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ))
    {t : ScheduleThresholds} {J : Set ℝ}
    (hf₀ : Function.support f₀ ⊆ J) :
    ∀ {n : ℕ} {x : ℝ},
      packetDensity φ f₀ t n x ≠ 0 →
      x ∈ finitePacketSet t J n := by
  intro n
  induction n with
  | zero =>
      intro x hx
      refine ⟨?_, ?_⟩
      · exact hf₀ (by simpa [Function.support] using hx)
      · intro k hk
        omega
  | succ n ih =>
      intro x hx
      have hprev : packetDensity φ f₀ t n x ≠ 0 := by
        intro hz
        apply hx
        simp [packetDensity_succ, hz]
      have hstage : concreteStagePacket φ t n x ≠ 0 := by
        intro hz
        apply hx
        simp [packetDensity_succ, hz]
      have hfinite := ih hprev
      refine ⟨hfinite.1, ?_⟩
      intro k hk
      by_cases hkn : k = n
      · subst k
        exact concreteStagePacket_ne_zero_implies_support hφ hstage
      · exact hfinite.2 k (by omega)

/-- The functional support of `f_n` is contained in the corresponding
finite packet intersection. -/
theorem support_packetDensity_subset_finitePacketSet
    {φ f₀ : ℝ → ℝ}
    (hφ : Function.support φ ⊆ Set.Ioo (-1 / 4 : ℝ) (1 / 4 : ℝ))
    {t : ScheduleThresholds} {J : Set ℝ}
    (hf₀ : Function.support f₀ ⊆ J) (n : ℕ) :
    Function.support (packetDensity φ f₀ t n) ⊆ finitePacketSet t J n := by
  intro x hx
  exact packetDensity_ne_zero_implies_mem_finitePacketSet hφ hf₀
    (by simpa [Function.support] using hx)


/-- The finite packet sets decrease with the number of imposed stages. -/
theorem antitone_finitePacketSet
    (t : ScheduleThresholds) (J : Set ℝ) :
    Antitone (finitePacketSet t J) := by
  intro m n hmn x hx
  refine ⟨hx.1, ?_⟩
  intro k hk
  exact hx.2 k (lt_of_lt_of_le hk hmn)

/-- A point lies in the full manuscript packet set exactly when it belongs to
every finite-stage packet set. -/
theorem mem_manuscriptPacketSet_iff_forall_mem_finitePacketSet
    {t : ScheduleThresholds} {J : Set ℝ} {x : ℝ} :
    x ∈ manuscriptPacketSet t J ↔
      ∀ n : ℕ, x ∈ finitePacketSet t J n := by
  constructor
  · intro hx n
    refine ⟨hx.1, ?_⟩
    intro k hk
    exact mem_iInter.mp hx.2 k
  · intro hx
    have hx0 := hx 0
    refine ⟨hx0.1, ?_⟩
    apply mem_iInter.mpr
    intro k
    exact (hx (k + 1)).2 k (by omega)

/-- The full packet set is the intersection of its finite-stage
approximations. -/
theorem iInter_finitePacketSet
    (t : ScheduleThresholds) (J : Set ℝ) :
    (⋂ n : ℕ, finitePacketSet t J n) = manuscriptPacketSet t J := by
  ext x
  rw [mem_iInter]
  exact mem_manuscriptPacketSet_iff_forall_mem_finitePacketSet.symm

end TNumbersLean
