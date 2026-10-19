module

public import PottsDiscontinuity.TorusCrossing.Mixture
public import PottsDiscontinuity.TorusCrossing.TorusBarrier
public import PottsDiscontinuity.TorusCrossing.TorusTranslate
public import PottsDiscontinuity.TorusRC.IndexedOpening
public import PottsDiscontinuity.TorusRC.TiltDuality

/-!
# The crossing estimate (3.19)

For every `q ≥ 1` there is `c > 0` such that for all even periods `N, M ≥ 4` and all `n ≥ 1`
with `3n ≤ min(N, M)`, the torus random-cluster measure at `p_c(q)` gives probability at least
`c` to a vertical open crossing of the rectangle `[0,3n] × [0,n]`.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open PottsDiscontinuity.TorusRC Torus CorrLength
open scoped Classical

variable {N M : ℕ}

theorem prob_cover (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E1 E2 E3 : Set (RCConfig N M)) (h : ∀ A, A ∈ E1 ∨ A ∈ E2 ∨ A ∈ E3) :
    1 ≤ torusRCProbability hN hM q E1 + torusRCProbability hN hM q E2 +
      torusRCProbability hN hM q E3 := by
  rw [torusRCProbability_eq_sum, torusRCProbability_eq_sum, torusRCProbability_eq_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc (1 : ℝ) = ∑ A, torusRCMass hN hM q A := (sum_torusRCMass hN hM q).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro A _
      have hm := (torusRCMass_pos hN hM q A).le
      have n1 : 0 ≤ E1.indicator (torusRCMass hN hM q) A := Set.indicator_nonneg (fun _ _ => (torusRCMass_pos hN hM q _).le) A
      have n2 : 0 ≤ E2.indicator (torusRCMass hN hM q) A := Set.indicator_nonneg (fun _ _ => (torusRCMass_pos hN hM q _).le) A
      have n3 : 0 ≤ E3.indicator (torusRCMass hN hM q) A := Set.indicator_nonneg (fun _ _ => (torusRCMass_pos hN hM q _).le) A
      rcases h A with h1 | h2 | h3
      · rw [Set.indicator_of_mem h1]; linarith
      · rw [Set.indicator_of_mem h2]; linarith
      · rw [Set.indicator_of_mem h3]; linarith

theorem prob_dual_le (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q {A | translatedDualConfig A ∈ E} ≤
      q.val ^ 2 * torusRCProbability hN hM q E := by
  have h := torusRCProbability_translatedDual_lower hN hM q E
  have hq : 0 < q.val ^ 2 := pow_pos (lt_of_lt_of_le zero_lt_one q.property) _
  rw [div_le_iff₀ hq] at h
  change torusRCProbability hN hM q (translatedDualConfig ⁻¹' E) ≤ _
  linarith

/-- The core estimate, for suitable parameters of the board. -/
theorem core_bound (q : Set.Ici (1 : ℝ)) (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (n s : ℕ) (hn : 0 < n) (hs : s % 2 = 1) (hs1 : s + 1 ≤ 3 * n)
    (hs2 : 2 * n < s) (hN3 : 3 * n ≤ N) (hM3 : 3 * n ≤ M)
    (ρF : ℤ) (hρFe : Even ρF) (hρF1 : (n : ℤ) - 1 ≤ ρF) (hρF2 : ρF + n ≤ (s : ℤ) - n + 1)
    (aT : ℤ) (haT : aT = 0 ∨ aT = 1) (hρTe : Even (aT + ((s : ℤ) - n))) :
    1 / (1 + q.val + 2 * q.val ^ 2) ≤
      torusRCProbability hN hM q {A | vCross hNp hMp n 0 0 A} := by
  set Q : Rect := ⟨0, 0, s, s⟩ with hQ
  have hg : Q.Geo n n := ⟨by simp [hQ]; omega, hn, hn, by simp [hQ]; omega⟩
  have hsq : Q.w = Q.h := rfl
  have hodd : Q.w % 2 = 1 := hs
  have hQN : Q.w + 1 ≤ N := by simp [hQ]; omega
  have hQM : Q.h + 1 ≤ M := by simp [hQ]; omega
  set p₀ := torusRCProbability hN hM q {A | vCross hNp hMp n 0 0 A} with hp₀
  have hq1 : 1 ≤ q.val := q.property
  have hq0 : 0 < q.val := lt_of_lt_of_le zero_lt_one hq1
  -- crossing event
  have hF : torusRCProbability hN hM q {A | Q.crossEv n n (boardOf Q hNp hMp A)} ≤ p₀ := by
    have hsub : {A | Q.crossEv n n (boardOf Q hNp hMp A)} ⊆ {A | vCross hNp hMp n 0 ρF A} := by
      intro A hA
      refine cross_to_vCross hNp hMp Q A n hn 0 ρF ⟨by simp [hQ], by simp [hQ]; omega⟩ ?_ ?_ hA
      · simp [hQ]; omega
      · simp [hQ]; omega
    exact (torusRCProbability_mono hN hM q hsub).trans
      (prob_vCross_le hN hM hNp hMp q n 0 ρF (by simpa using hρFe))
  -- the barriers
  have hB : torusRCProbability hN hM q {A | ¬ Q.barB n (boardOf Q hNp hMp A)} ≤ q.val ^ 2 * p₀ := by
    have hsub : {A | ¬ Q.barB n (boardOf Q hNp hMp A)} ⊆
        {A | translatedDualConfig A ∈ {A | vCross hNp hMp n 0 0 A}} := by
      intro A hA
      exact notBarB_to_vCross hNp hMp Q A hg n hn 0 0 ⟨by simp [hQ], by simp [hQ]; omega⟩
        (by simp [hQ]) (by simp [hQ]) hA
    exact (torusRCProbability_mono hN hM q hsub).trans (prob_dual_le hN hM q _)
  have hT : torusRCProbability hN hM q {A | ¬ Q.barT n (boardOf Q hNp hMp A)} ≤ q.val ^ 2 * p₀ := by
    have hsub : {A | ¬ Q.barT n (boardOf Q hNp hMp A)} ⊆
        {A | translatedDualConfig A ∈ {A | vCross hNp hMp n aT ((s : ℤ) - n) A}} := by
      intro A hA
      refine notBarT_to_vCross hNp hMp Q A hg n hn aT ((s : ℤ) - n)
        ⟨by simp [hQ]; omega, by simp [hQ]; omega⟩ (by simp [hQ]) (by simp [hQ]) hA
    calc _ ≤ _ := torusRCProbability_mono hN hM q hsub
      _ ≤ q.val ^ 2 * torusRCProbability hN hM q {A | vCross hNp hMp n aT ((s : ℤ) - n) A} :=
          prob_dual_le hN hM q _
      _ ≤ q.val ^ 2 * p₀ := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact prob_vCross_le hN hM hNp hMp q n aT ((s : ℤ) - n) hρTe
  -- covering
  have hcov := prob_cover hN hM q {A | Q.barAll n n (boardOf Q hNp hMp A)}
    {A | ¬ Q.barB n (boardOf Q hNp hMp A)} {A | ¬ Q.barT n (boardOf Q hNp hMp A)} (by
      intro A
      by_cases h1 : Q.barB n (boardOf Q hNp hMp A)
      · by_cases h2 : Q.barT n (boardOf Q hNp hMp A)
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl h1))
  -- the board estimate
  have hbl := torus_bl q hN hM hNp hMp hN4 hM4 Q hg hQN hQM
  have hκ : 1 / (1 + q.val) ≤ (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal :=
    Rect.crossing_ge Q q hsq hodd (by simp [hQ]; omega)
  set κ := (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal with hκd
  set Pbar := torusRCProbability hN hM q {A | Q.barAll n n (boardOf Q hNp hMp A)} with hPbar
  have hPbar : 1 - 2 * (q.val ^ 2 * p₀) ≤ Pbar := by linarith
  have hmain : κ * Pbar ≤ p₀ := hbl.trans hF
  have hPnn : 0 ≤ Pbar := torusRCProbability_nonneg hN hM q _
  have hp0nn : 0 ≤ p₀ := torusRCProbability_nonneg hN hM q _
  -- final algebra
  have hc0 : 0 < 1 / (1 + q.val) := by positivity
  rw [div_le_iff₀ (by positivity)]
  by_cases hcase : 1 - 2 * (q.val ^ 2 * p₀) ≤ 0
  · nlinarith [sq_nonneg q.val]
  · push Not at hcase
    have h1 : 1 / (1 + q.val) * (1 - 2 * (q.val ^ 2 * p₀)) ≤ κ * Pbar := by
      calc _ ≤ κ * (1 - 2 * (q.val ^ 2 * p₀)) :=
            mul_le_mul_of_nonneg_right hκ hcase.le
        _ ≤ κ * Pbar := mul_le_mul_of_nonneg_left hPbar (hc0.le.trans hκ)
    have h2 : 1 / (1 + q.val) * (1 - 2 * (q.val ^ 2 * p₀)) ≤ p₀ := h1.trans hmain
    have h3 : 1 - 2 * (q.val ^ 2 * p₀) ≤ (1 + q.val) * p₀ := by
      have := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 1 + q.val by positivity)
      field_simp at this
      linarith
    nlinarith

/-- The case `n = 1`: a single open edge. -/
theorem one_bound (q : Set.Ici (1 : ℝ)) (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) :
    fkOpenEnergy (torusRCBridgeParameters q) ≤
      torusRCProbability hN hM q {A | vCross hNp hMp 1 0 0 A} := by
  have h := torusRCProbability_allOpen_ge hN hM hN4 hM4 q
    {(periodicCoordinate hNp 1, periodicCoordinate hMp 1)}
  rw [Finset.card_singleton, pow_one] at h
  refine h.trans (torusRCProbability_mono hN hM q ?_)
  intro A hA
  have hA' : A (periodicCoordinate hNp 1, periodicCoordinate hMp 1) = true :=
    hA _ (Finset.mem_singleton_self _)
  let u : RotatedVertex := ⟨(0, 0), ⟨0, rfl⟩⟩
  let v : RotatedVertex := ⟨(1, 1), ⟨1, rfl⟩⟩
  have hadj : (liftedStripGraph hNp hMp A 0 (0 + 3 * ((1 : ℕ) : ℤ))).Adj u v := by
    refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · change |(0 : ℤ) - 1| = 1 ∧ |(0 : ℤ) - 1| = 1
      norm_num
    · change A (periodicCoordinate hNp (max 0 1), periodicCoordinate hMp (max 0 1)) = true
      simpa using hA'
    all_goals norm_num
  refine ⟨u, v, rfl, rfl, SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
  intro z hz
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;> constructor <;> norm_num [u, v]

/-- **Equation (3.19)**: the crossing estimate for the torus. -/
theorem h319_proved (q : Set.Ici (1 : ℝ)) : h319 q := by
  have hq1 : 1 ≤ q.val := q.property
  have hq0 : 0 < q.val := lt_of_lt_of_le zero_lt_one hq1
  refine ⟨min (fkOpenEnergy (torusRCBridgeParameters q)) (1 / (1 + q.val + 2 * q.val ^ 2)),
    lt_min (fkOpenEnergy_pos _) (by positivity), ?_⟩
  intro N M n hN hM hN4 hM4 hn h3N h3M hNpos hMpos
  show _ ≤ torusRCProbability hN hM q {A | torusRCVerticalRectangleCrossing hNpos hMpos n A}
  have heq : {A | torusRCVerticalRectangleCrossing hNpos hMpos n A} =
      {A | vCross hNpos hMpos n 0 0 A} := by
    ext A; exact (vCross_zero_iff hNpos hMpos n A).symm
  rw [heq]
  by_cases hn1 : n = 1
  · subst hn1
    exact (min_le_left _ _).trans (one_bound q hN hM hNpos hMpos hN4 hM4)
  · refine (min_le_right _ _).trans ?_
    have hn2 : 2 ≤ n := by omega
    rcases Nat.even_or_odd n with he | ho
    · refine core_bound q hN hM hNpos hMpos hN4 hM4 n (3 * n - 1) hn (by obtain ⟨k, hk⟩ := he; omega)
        (by omega) (by omega) h3N h3M (n : ℤ) (by exact_mod_cast he) (by omega) (by omega) 1
        (Or.inr rfl) ?_
      obtain ⟨k, hk⟩ := he
      exact ⟨n, by omega⟩
    · have hn3 : 3 ≤ n := by obtain ⟨k, hk⟩ := ho; omega
      refine core_bound q hN hM hNpos hMpos hN4 hM4 n (3 * n - 2) hn (by obtain ⟨k, hk⟩ := ho; omega)
        (by omega) (by omega) h3N h3M ((n : ℤ) - 1) ?_ (by omega) (by omega) 0 (Or.inl rfl) ?_
      · obtain ⟨k, hk⟩ := ho; exact ⟨k, by omega⟩
      · obtain ⟨k, hk⟩ := ho; exact ⟨2 * k, by omega⟩

end PottsDiscontinuity.TorusCrossing
