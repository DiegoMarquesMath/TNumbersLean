import TNumbersLean.HeightRangeCoverage

noncomputable section

namespace TNumbersLean

/-- The explicit constant in (3.9). -/
def propositionB (n : ℕ) : ℝ :=
  (n : ℝ) + 2 + 40000 * ((n : ℝ) + 1)^5 * ((n : ℝ) + 2)

/-- The recurrent-degree lower exponent in (3.11). -/
def recurrentW (d : ℕ) : ℝ := ((d : ℝ) + 1)^3 / (d : ℝ) - 1

theorem propositionB_eq (n : ℕ) :
    propositionB n = (n : ℝ) + 2 + (K (n : ℝ) + 1) / delta (n : ℝ) := by
  rw [B_exponent_identity (n : ℝ) (by positivity)]
  rfl

namespace CriterionInputs

variable {S : AlgebraicApproximationSystem} {s : CriterionSchedule} {x : ℝ}
    (I : CriterionInputs S s x)

include I in
/-- The genuine triangle-inequality estimate (3.12). -/
theorem local_separation (n k : ℕ) (hn : 1 ≤ n) (hk : DegreeAdmissible s.d n k)
    (β : ℝ) (ha : S.isAlg β) (hd : S.degree β ≤ n) :
    s.Q k ^ (-K (n : ℝ) - 1) * S.height β ^ (-(n : ℝ) - 2) -
      (1 / 4 : ℝ) * s.Q k ^ (-(s.A k : ℝ)) ≤ |x - β| := by
  have hs := I.translated_center_separation n k hn hk β ha hd
  have he := I.source_approximation_Q k
  have ht : |I.center k - β| ≤ |x - I.center k| + |x - β| := by
    simpa only [abs_sub_comm (I.center k) x] using abs_sub_le (I.center k) x β
  linarith

/-- Multiplying the manuscript error ratio by the separation term gives the error. -/
theorem source_error_factorization (n k : ℕ) (H : ℝ) (hH : 0 < H) :
    ((1 / 4 : ℝ) * s.Q k ^ (K (n : ℝ) + 1 - (s.A k : ℝ)) * H ^ ((n : ℝ) + 2)) *
      (s.Q k ^ (-K (n : ℝ) - 1) * H ^ (-(n : ℝ) - 2)) =
      (1 / 4 : ℝ) * s.Q k ^ (-(s.A k : ℝ)) := by
  calc
    _ = (1 / 4 : ℝ) *
        (s.Q k ^ (K (n : ℝ) + 1 - (s.A k : ℝ)) * s.Q k ^ (-K (n : ℝ) - 1)) *
        (H ^ ((n : ℝ) + 2) * H ^ (-(n : ℝ) - 2)) := by ring
    _ = _ := by
      rw [← Real.rpow_add (s.scale_pos k), ← Real.rpow_add hH]
      simp [show K (n : ℝ) + 1 - (s.A k : ℝ) + (-K (n : ℝ) - 1) = -(s.A k : ℝ) by ring,
        show (n : ℝ) + 2 + (-(n : ℝ) - 2) = 0 by ring]

/-- Both inequalities in the error-ratio calculation preceding (3.14). -/
theorem source_error_ratio_bound (n k : ℕ) (H : ℝ) (hH : 0 < H)
    (hupper : H ≤ s.heightRight n k) :
    (1 / 4 : ℝ) * s.Q k ^ (K (n : ℝ) + 1 - (s.A k : ℝ)) * H ^ ((n : ℝ) + 2) ≤
      (1 / 4 : ℝ) * s.Q k ^ (-2 : ℝ) ∧
      (1 / 4 : ℝ) * s.Q k ^ (-2 : ℝ) ≤ 1 / 2 := by
  have hQ := s.scale_pos k
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hp : H ^ ((n : ℝ) + 2) ≤ s.Q k ^ ((s.A k : ℝ) - K (n : ℝ) - 3) := by
    calc
      H ^ ((n : ℝ) + 2) ≤ (s.Q k ^ s.usableExponent n k) ^ ((n : ℝ) + 2) :=
        Real.rpow_le_rpow hH.le hupper hden.le
      _ = _ := by
        rw [← Real.rpow_mul (s.scale_pos k).le]
        unfold CriterionSchedule.usableExponent
        rw [div_mul_cancel₀ _ (ne_of_gt hden)]
  constructor
  · calc
      _ ≤ (1 / 4 : ℝ) * s.Q k ^ (K (n : ℝ) + 1 - (s.A k : ℝ)) *
          s.Q k ^ ((s.A k : ℝ) - K (n : ℝ) - 3) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add (s.scale_pos k)]
        congr 2
        ring
  · have hp1 : s.Q k ^ (-2 : ℝ) ≤ 1 := by
      calc
        _ ≤ s.Q k ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (s.scale_ge_one k) (by norm_num)
        _ = 1 := Real.rpow_zero _
    linarith

include I in
/-- The absorbed local bound (3.14), derived without any stronger input. -/
theorem absorbed_local_bound (n k : ℕ) (hn : 1 ≤ n) (hk : DegreeAdmissible s.d n k)
    (β : ℝ) (ha : S.isAlg β) (hd : S.degree β ≤ n)
    (hupper : S.height β ≤ s.heightRight n k) :
    (1 / 2 : ℝ) * s.Q k ^ (-K (n : ℝ) - 1) * S.height β ^ (-(n : ℝ) - 2) ≤ |x - β| := by
  have hQ := s.scale_pos k
  have hH : 0 < S.height β := lt_of_lt_of_le (by norm_num) (S.height_ge_one β ha)
  have hr := source_error_ratio_bound (s := s) n k (S.height β) hH hupper
  have hf := source_error_factorization (s := s) n k (S.height β) hH
  have hm : 0 ≤ s.Q k ^ (-K (n : ℝ) - 1) * S.height β ^ (-(n : ℝ) - 2) := by positivity
  have he := mul_le_mul_of_nonneg_right (hr.1.trans hr.2) hm
  rw [hf] at he
  have hl := I.local_separation n k hn hk β ha hd
  nlinarith

/-- A fixed positive exponent below all admissible usable exponents. -/
theorem usableExponent_uniform_lower (n k : ℕ) (hk : DegreeAdmissible s.d n k) :
    ((n : ℝ) + 2)^3 / (2 * ((n : ℝ) + 2)) ≤ s.usableExponent n k := by
  have hA : ((n : ℝ) + 2)^3 ≤ (s.A k : ℝ) := by
    exact_mod_cast admissible_exponent_lower (s := s) n k hk
  exact (div_le_div_of_nonneg_right hA (by positivity)).trans
    (usable_exponent_lower (s := s) n k hk)

/-- Right endpoints eventually exceed every fixed height at admissible stages. -/
theorem eventually_admissible_heightRight_ge (n : ℕ) (H : ℝ) :
    ∃ N, ∀ k ≥ N, DegreeAdmissible s.d n k → H ≤ s.heightRight n k := by
  have hc : 0 < ((n : ℝ) + 2)^3 / (2 * ((n : ℝ) + 2)) := by positivity
  have ht := (tendsto_rpow_atTop hc).comp s.scale_tends_to_infinity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_ge_atTop H))
  refine ⟨N, fun k hk ha => (hN k hk).trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le (s.scale_ge_one k)
    (usableExponent_uniform_lower (s := s) n k ha)

include I in
/-- Transcendence, proved by applying (3.14) to beta=x at a late admissible stage. -/
theorem transcendence : ¬ S.isAlg x := by
  intro hx
  have hn := S.degree_pos x hx
  obtain ⟨N, hN⟩ := eventually_admissible_heightRight_ge (s := s) (S.degree x) (S.height x)
  obtain ⟨k, hk, ha⟩ := s.exists_admissible_ge (S.degree x) hn N
  have hl := I.absorbed_local_bound (S.degree x) k hn ha x hx le_rfl (hN k hk ha)
  have hp : 0 < (1 / 2 : ℝ) * s.Q k ^ (-K (S.degree x : ℝ) - 1) *
      S.height x ^ (-(S.degree x : ℝ) - 2) := by
    apply mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (s.scale_pos k) _))
      (Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) (S.height_ge_one x hx)) _)
  have : 0 < |x - x| := hp.trans_le hl
  simp at this

/-- Convert the left-endpoint inequality to the negative scale factor in (3.19). -/
theorem covered_scale_factor (n k : ℕ) (H : ℝ) (_hH : 0 < H)
    (hleft : s.heightLeft n k ≤ H) :
    H ^ (-(K (n : ℝ) + 1) / delta (n : ℝ)) ≤ s.Q k ^ (-K (n : ℝ) - 1) := by
  have hdelta := CriterionSchedule.height_delta_pos n
  have hK : 0 ≤ K (n : ℝ) := by unfold K; positivity
  have hex : -(K (n : ℝ) + 1) / delta (n : ℝ) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hdelta.le
  calc
    _ ≤ (s.Q k ^ delta (n : ℝ)) ^ (-(K (n : ℝ) + 1) / delta (n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_nonpos
        (Real.rpow_pos_of_pos (s.scale_pos k) _) hleft hex
    _ = _ := by
      rw [← Real.rpow_mul (s.scale_pos k).le]
      congr 1
      field_simp [ne_of_gt hdelta]
      ring

/-- At H >= 2, the factor 1/2 is absorbed by one additional inverse power. -/
theorem height_half_absorption (H B : ℝ) (hH : 2 ≤ H) :
    H ^ (-B - 1) ≤ (1 / 2 : ℝ) * H ^ (-B) := by
  have hp : 0 < H := by linarith
  have hi : H⁻¹ ≤ (1 / 2 : ℝ) := by
    have := (inv_le_inv₀ hp (by norm_num : (0 : ℝ) < 2)).2 hH
    norm_num at this ⊢
    exact this
  rw [show -B - 1 = -B + (-1) by ring, Real.rpow_add hp, Real.rpow_neg_one]
  nlinarith [mul_le_mul_of_nonneg_left hi (Real.rpow_pos_of_pos hp (-B)).le]

/-- Exact global exclusion (3.10)/(3.19), with a threshold uniform in beta. -/
theorem global_separation_uniform (n : ℕ) (hn : 1 ≤ n) :
    ∃ H₀ : ℝ, 2 ≤ H₀ ∧ ∀ {y : ℝ}, ∀ _ : CriterionInputs S s y,
      ∀ β, S.isAlg β → S.degree β ≤ n → H₀ ≤ S.height β →
        S.height β ^ (-propositionB n - 1) ≤ |y - β| := by
  obtain ⟨H₀, hH₀, hcover⟩ := s.exists_height_cover n hn 0
  refine ⟨H₀, hH₀, ?_⟩
  intro y J β ha hd hheight
  have hH2 : 2 ≤ S.height β := hH₀.trans hheight
  have hH : 0 < S.height β := by linarith
  obtain ⟨k, _, hk, hleft, hright⟩ := hcover (S.height β) hheight
  have hl := J.absorbed_local_bound n k hn hk β ha hd hright
  have hs := covered_scale_factor (s := s) n k (S.height β) hH hleft
  calc
    S.height β ^ (-propositionB n - 1) ≤ (1 / 2 : ℝ) * S.height β ^ (-propositionB n) :=
      height_half_absorption (S.height β) (propositionB n) hH2
    _ = (1 / 2 : ℝ) * S.height β ^ (-(K (n : ℝ) + 1) / delta (n : ℝ)) *
        S.height β ^ (-(n : ℝ) - 2) := by
      rw [mul_assoc, ← Real.rpow_add hH, propositionB_eq]
      congr 2
      ring
    _ ≤ (1 / 2 : ℝ) * s.Q k ^ (-K (n : ℝ) - 1) * S.height β ^ (-(n : ℝ) - 2) := by
      gcongr
    _ ≤ |y - β| := hl

include I in
/-- The uniform theorem specialized to the current point. -/
theorem global_separation (n : ℕ) (hn : 1 ≤ n) :
    ∃ H₀ : ℝ, 2 ≤ H₀ ∧ ∀ β, S.isAlg β → S.degree β ≤ n → H₀ ≤ S.height β →
      S.height β ^ (-propositionB n - 1) ≤ |x - β| := by
  obtain ⟨H₀, hH₀, hbound⟩ := global_separation_uniform (S := S) (s := s) n hn
  exact ⟨H₀, hH₀, hbound I⟩

include I in
/-- The first bound of (3.11), with Northcott used only in the exponent bridge. -/
theorem upper_wStar_bound (n : ℕ) (hn : 1 ≤ n) :
    S.wStar x n ≤ (propositionB n : EReal) := by
  obtain ⟨H₀, _, hbound⟩ := I.global_separation n hn
  exact S.upper_bound_bridge x (propositionB n) H₀ n hbound

include I in
theorem wStar_lt_top (n : ℕ) (hn : 1 ≤ n) : S.wStar x n < ⊤ :=
  (I.upper_wStar_bound n hn).trans_lt (EReal.coe_lt_top _)

/-- The denominators diverge by their lower comparison with Q. -/
theorem denominator_tends_to_infinity :
    Filter.Tendsto (fun k => (I.q k : ℝ)) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono (fun k => I.denominator_lower k) s.scale_tends_to_infinity

/-- All center heights diverge, using exact-degree height lower bounds. -/
theorem center_height_tends_to_infinity :
    Filter.Tendsto (fun k => S.height (I.center k)) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono _ I.denominator_tends_to_infinity
  intro k
  calc
    (I.q k : ℝ) = (I.q k : ℝ) ^ (1 : ℕ) := (pow_one _).symm
    _ ≤ (I.q k : ℝ) ^ s.d k := pow_le_pow_right₀
      ((s.scale_ge_one k).trans (I.denominator_lower k)) (by have := s.degree_ge_two k; omega)
    _ ≤ S.height (I.center k) := I.center_height_lower k

/-- Arbitrarily late recurrent centers have heights above every real bound. -/
theorem recurrent_center_heights_unbounded (d N : ℕ) (hd : 2 ≤ d) (H : ℝ) :
    ∃ k ≥ N, s.d k = d ∧ H < S.height (I.center k) := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (I.center_height_tends_to_infinity.eventually (Filter.eventually_gt_atTop H))
  obtain ⟨k, hk, hlarge⟩ := (s.recurrent d hd).exists_gt (max N M)
  exact ⟨k, (le_max_left N M).trans hlarge.le, hk,
    hM k ((le_max_right N M).trans hlarge.le)⟩

/-- Infinitely many distinct exact-degree center values on every recurrent tail.
Finitely many values would have bounded heights, contradicting the preceding theorem. -/
theorem recurrent_centers_infinite (d N : ℕ) (hd : 2 ≤ d) :
    (I.center '' {k | N ≤ k ∧ s.d k = d}).Infinite := by
  intro hf
  obtain ⟨H, hH⟩ := (hf.image S.height).bddAbove
  obtain ⟨k, hk, hkd, hheight⟩ := I.recurrent_center_heights_unbounded d N hd H
  have hm : S.height (I.center k) ∈ S.height '' (I.center '' {k | N ≤ k ∧ s.d k = d}) :=
    ⟨I.center k, ⟨k, ⟨hk, hkd⟩, rfl⟩, rfl⟩
  exact (not_le_of_gt hheight) (hH hm)

/-- Source approximation at a recurrent degree, with its fixed cubic exponent. -/
theorem recurrent_source_bound (d k : ℕ) (hkd : s.d k = d) :
    |x - I.center k| ≤ (1 / 4 : ℝ) * (I.q k : ℝ) ^ (-((d : ℝ) + 1)^3) := by
  simpa only [s.exponent_eq k, stageExponent, hkd, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    using I.source_approximation k

/-- Strict approximation for every w<W_d, treating both signs of w+1. -/
theorem eventually_recurrent_strong_approximation (d : ℕ) (hd : 2 ≤ d)
    (w : ℝ) (hw : w < recurrentW d) :
    ∃ N, ∀ k ≥ N, s.d k = d →
      0 < |x - I.center k| ∧ |x - I.center k| < S.height (I.center k) ^ (-w - 1) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hApos : 0 < ((d : ℝ) + 1)^3 := by positivity
  have hgap : 0 < ((d : ℝ) + 1)^3 - (d : ℝ) * (w + 1) := by
    have hwd : w + 1 < ((d : ℝ) + 1)^3 / (d : ℝ) := by
      unfold recurrentW at hw
      linarith
    have := (lt_div_iff₀ hdpos).mp hwd
    nlinarith
  have herrpos : ∀ k, 0 < |x - I.center k| := by
    intro k
    apply abs_pos.mpr
    apply sub_ne_zero.mpr
    intro he
    apply I.transcendence
    rw [he]
    exact I.center_algebraic k
  by_cases hsign : 0 ≤ w + 1
  · have hC : 0 < I.heightConstant d := lt_of_lt_of_le (by norm_num) (I.heightConstant_ge_one d hd)
    have ht := (tendsto_rpow_atTop hgap).comp I.denominator_tends_to_infinity
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (ht.eventually (Filter.eventually_gt_atTop (I.heightConstant d ^ (w + 1))))
    refine ⟨N, fun k hk hkd => ⟨herrpos k, ?_⟩⟩
    have hq : 0 < (I.q k : ℝ) := by exact_mod_cast I.denominator_pos k
    have hH : 0 < S.height (I.center k) :=
      lt_of_lt_of_le (by norm_num) (S.height_ge_one _ (I.center_algebraic k))
    have hcanc : I.heightConstant d ^ (-w - 1) * I.heightConstant d ^ (w + 1) = 1 := by
      rw [← Real.rpow_add hC]
      simp [show -w - 1 + (w + 1) = 0 by ring]
    have hratio : (1 / 4 : ℝ) < I.heightConstant d ^ (-w - 1) *
        (I.q k : ℝ) ^ (((d : ℝ) + 1)^3 - (d : ℝ) * (w + 1)) := by
      calc
        (1 / 4 : ℝ) < 1 := by norm_num
        _ = I.heightConstant d ^ (-w - 1) * I.heightConstant d ^ (w + 1) := hcanc.symm
        _ < _ := mul_lt_mul_of_pos_left (hN k hk) (Real.rpow_pos_of_pos hC _)
    have hhupper : S.height (I.center k) ≤ I.heightConstant d * (I.q k : ℝ) ^ d := by
      simpa only [hkd] using I.center_height_upper k
    calc
      |x - I.center k| ≤ (1 / 4 : ℝ) * (I.q k : ℝ) ^ (-((d : ℝ) + 1)^3) :=
        I.recurrent_source_bound d k hkd
      _ < (I.heightConstant d ^ (-w - 1) *
          (I.q k : ℝ) ^ (((d : ℝ) + 1)^3 - (d : ℝ) * (w + 1))) *
          (I.q k : ℝ) ^ (-((d : ℝ) + 1)^3) :=
        mul_lt_mul_of_pos_right hratio (Real.rpow_pos_of_pos hq _)
      _ = I.heightConstant d ^ (-w - 1) * (I.q k : ℝ) ^ ((d : ℝ) * (-w - 1)) := by
        rw [mul_assoc, ← Real.rpow_add hq]
        congr 2
        ring
      _ = (I.heightConstant d * (I.q k : ℝ) ^ d) ^ (-w - 1) := by
        rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
      _ ≤ S.height (I.center k) ^ (-w - 1) :=
        Real.rpow_le_rpow_of_exponent_nonpos hH hhupper (by linarith)
  · refine ⟨0, fun k _ hkd => ⟨herrpos k, ?_⟩⟩
    have hq1 : 1 ≤ (I.q k : ℝ) := (s.scale_ge_one k).trans (I.denominator_lower k)
    have hqpow : (I.q k : ℝ) ^ (-((d : ℝ) + 1)^3) ≤ 1 := by
      calc
        _ ≤ (I.q k : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
        _ = 1 := Real.rpow_zero _
    have hheight : 1 ≤ S.height (I.center k) ^ (-w - 1) := by
      calc
        1 = S.height (I.center k) ^ (0 : ℝ) := (Real.rpow_zero _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
          (S.height_ge_one _ (I.center_algebraic k)) (by linarith)
    have he := I.recurrent_source_bound d k hkd
    have herr : |x - I.center k| ≤ (1 / 4 : ℝ) := by nlinarith
    exact (lt_of_le_of_lt herr (by norm_num : (1 / 4 : ℝ) < 1)).trans_le hheight

include I in
/-- Infinitely many distinct strict approximants of exact degree d. -/
theorem recurrent_exact_approximants_infinite (d : ℕ) (hd : 2 ≤ d)
    (w : ℝ) (hw : w < recurrentW d) :
    {α | S.isAlg α ∧ S.degree α = d ∧
      0 < |x - α| ∧ |x - α| < S.height α ^ (-w - 1)}.Infinite := by
  obtain ⟨N, hN⟩ := I.eventually_recurrent_strong_approximation d hd w hw
  apply (I.recurrent_centers_infinite d N hd).mono
  rintro α ⟨k, ⟨hk, hkd⟩, rfl⟩
  have he := hN k hk hkd
  exact ⟨I.center_algebraic k, (I.center_exact_degree k).trans hkd, he⟩

include I in
/-- Infinitude in the degree-at-most-d sense of definition (1.1). -/
theorem recurrent_approximants_infinite (d : ℕ) (hd : 2 ≤ d)
    (w : ℝ) (hw : w < recurrentW d) : (S.approximants x d w).Infinite := by
  apply (I.recurrent_exact_approximants_infinite d hd w hw).mono
  rintro α ⟨ha, hdegree, hpos, herror⟩
  exact ⟨ha, hdegree.le, hpos, herror⟩

include I in
/-- The recurrent-degree bound, exactly the second inequality of (3.11). -/
theorem lower_wStar_bound (d : ℕ) (hd : 2 ≤ d) :
    (recurrentW d : EReal) ≤ S.wStar x d :=
  S.lower_bound_bridge x (recurrentW d) d (fun w hw => I.recurrent_approximants_infinite d hd w hw)

include I in
/-- Division of the lower exponent bound, the first inequality of (3.20). -/
theorem normalized_lower_bound (d : ℕ) (hd : 2 ≤ d) :
    (((d : ℝ) + 1)^3 / (d : ℝ)^2 - 1 / (d : ℝ) : ℝ) ≤ S.normalizedWStar x d := by
  have hp : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hdiv := EReal.div_le_div_right_of_nonneg
    (show (0 : EReal) ≤ (d : EReal) by exact_mod_cast (show 0 ≤ d from Nat.zero_le d))
    (I.lower_wStar_bound d hd)
  have heq : recurrentW d / (d : ℝ) = ((d : ℝ) + 1)^3 / (d : ℝ)^2 - 1 / (d : ℝ) := by
    unfold recurrentW
    field_simp [ne_of_gt hp]
  rw [← heq, EReal.coe_div, EReal.coe_coe_eq_natCast]
  exact hdiv

include I in
/-- The existing normalized numerical budget makes the bound at least d. -/
theorem normalized_ge_degree (d : ℕ) (hd : 2 ≤ d) :
    (d : EReal) ≤ S.normalizedWStar x d := by
  have hp : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hn := normalized_lower_ge (d : ℝ) hp
  have hc : (d : EReal) ≤ ((((d : ℝ) + 1)^3 / (d : ℝ)^2 - 1 / (d : ℝ) : ℝ) : EReal) := by
    exact_mod_cast hn
  exact hc.trans (I.normalized_lower_bound d hd)

include I in
/-- Explicit tail-unboundedness, choosing the degree beyond both N and R. -/
theorem normalized_tail_unbounded : ∀ R : ℝ, ∀ N : ℕ, ∃ n ≥ N,
    (R : EReal) ≤ S.normalizedWStar x n := by
  intro R N
  obtain ⟨m, hm⟩ := exists_nat_ge R
  let n := max 2 (max N m)
  have hn2 : 2 ≤ n := le_max_left _ _
  have hN : N ≤ n := (le_max_left N m).trans (le_max_right _ _)
  have hmN : m ≤ n := (le_max_right N m).trans (le_max_right _ _)
  have hR : R ≤ (n : ℝ) := hm.trans (by exact_mod_cast hmN)
  exact ⟨n, hN, (by exact_mod_cast hR : (R : EReal) ≤ (n : EReal)).trans (I.normalized_ge_degree n hn2)⟩

include I in
/-- The stronger limit assertion stated at the end of Proposition 3.2. -/
theorem normalized_tends_to_top :
    Filter.Tendsto (S.normalizedWStar x) Filter.atTop (nhds (⊤ : EReal)) := by
  apply EReal.tendsto_nhds_top_iff_real.mpr
  intro R
  obtain ⟨m, hm⟩ := exists_nat_gt R
  apply Filter.eventually_atTop.mpr
  refine ⟨max 2 m, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := (le_max_left 2 m).trans hn
  have hmn : m ≤ n := (le_max_right 2 m).trans hn
  have hR : R < (n : ℝ) := hm.trans_le (by exact_mod_cast hmn)
  exact (by exact_mod_cast hR : (R : EReal) < (n : EReal)).trans_le (I.normalized_ge_degree n hn2)

include I in
theorem isTNumber : S.IsTNumber x :=
  S.t_number_bridge x I.transcendence (fun n hn => I.wStar_lt_top n hn) I.normalized_tail_unbounded

end CriterionInputs

/-- Proposition 3.2 from the declared Section 2 and schedule interfaces.
The global threshold depends only on the schedule and degree, not on x or beta. -/
theorem proposition_three_two {S : AlgebraicApproximationSystem} {s : CriterionSchedule}
    {x : ℝ} (I : CriterionInputs S s x) :
    (¬ S.isAlg x) ∧
    (∀ n, 1 ≤ n → ∃ Hₙ : ℝ, 2 ≤ Hₙ ∧ ∀ β,
      S.isAlg β → S.degree β ≤ n → Hₙ ≤ S.height β →
        S.height β ^ (-propositionB n - 1) ≤ |x - β|) ∧
    (∀ n, 1 ≤ n → S.wStar x n ≤ (propositionB n : EReal)) ∧
    (∀ d, 2 ≤ d → (recurrentW d : EReal) ≤ S.wStar x d) ∧
    (∀ R : ℝ, ∀ N : ℕ, ∃ n ≥ N, (R : EReal) ≤ S.normalizedWStar x n) ∧
    Filter.Tendsto (S.normalizedWStar x) Filter.atTop (nhds (⊤ : EReal)) ∧
    Filter.limsup (S.normalizedWStar x) Filter.atTop = ⊤ ∧ S.IsTNumber x := by
  exact ⟨I.transcendence, I.global_separation, I.upper_wStar_bound, I.lower_wStar_bound,
    I.normalized_tail_unbounded, I.normalized_tends_to_top, I.isTNumber.2.2, I.isTNumber⟩

end TNumbersLean
