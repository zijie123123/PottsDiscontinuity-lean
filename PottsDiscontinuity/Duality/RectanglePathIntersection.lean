/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import FixedPointTheorems.brouwer

@[expose] public section

open Set Topology unitInterval

namespace PottsDiscontinuity.FK.Curves

noncomputable section

def unitClamp (x : ℝ) : ℝ := max 0 (min 1 x)

lemma unitClamp_mem (x : ℝ) : unitClamp x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · apply max_le
    · norm_num
    · exact min_le_left _ _

lemma unitClamp_eq_zero_iff (x : ℝ) : unitClamp x = 0 ↔ x ≤ 0 := by
  simp [unitClamp, min_le_iff]

lemma unitClamp_eq_one_iff (x : ℝ) : unitClamp x = 1 ↔ 1 ≤ x := by
  constructor
  · intro h
    by_cases hx0 : x ≤ 0
    · have hz := (unitClamp_eq_zero_iff x).2 hx0
      rw [hz] at h
      norm_num at h
    · by_cases hx1 : x < 1
      · have hx0' : 0 < x := lt_of_not_ge hx0
        have hc : unitClamp x = x := by
          simp [unitClamp, max_eq_right (le_of_lt hx0'), min_eq_right (le_of_lt hx1)]
        rw [hc] at h
        linarith
      · exact le_of_not_gt hx1
  · intro hx
    simp [unitClamp, min_eq_left hx]

lemma unitClamp_eq_self_of_mem (x y : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (h : unitClamp y = x) : y = x := by
  rcases hx with ⟨hx0, hx1⟩
  by_cases hy0 : y ≤ 0
  · have : unitClamp y = 0 := (unitClamp_eq_zero_iff y).2 hy0
    rw [this] at h
    linarith
  by_cases hy1 : 1 ≤ y
  · have : unitClamp y = 1 := (unitClamp_eq_one_iff y).2 hy1
    rw [this] at h
    linarith
  · have hy0' : 0 < y := lt_of_not_ge hy0
    have hy1' : y < 1 := lt_of_not_ge hy1
    have hc : unitClamp y = y := by
      simp [unitClamp, max_eq_right (le_of_lt hy0'), min_eq_right (le_of_lt hy1')]
    rw [hc] at h
    exact h


lemma continuous_unitClamp : Continuous unitClamp := by
  unfold unitClamp
  fun_prop

lemma unitClamp_fixed_zero_of_signs (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (h : unitClamp (x - y) = x)
    (hzero : x = 0 → y ≤ 0) (hone : x = 1 → 0 ≤ y) : y = 0 := by
  rcases hx with ⟨hx0, hx1⟩
  by_cases hxz : x = 0
  · subst x
    have hy : unitClamp (0 - y) = 0 := h
    have hneg : 0 - y ≤ 0 := (unitClamp_eq_zero_iff _).mp hy
    have hsign := hzero rfl
    linarith
  by_cases hxo : x = 1
  · subst x
    have hy : unitClamp (1 - y) = 1 := h
    have hone' := hone rfl
    have hpos : 1 ≤ 1 - y := (unitClamp_eq_one_iff _).mp hy
    linarith
  · have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨lt_of_le_of_ne hx0 (Ne.symm hxz),
        lt_of_le_of_ne hx1 hxo⟩
    have heq := unitClamp_eq_self_of_mem x (x - y) hxIoo h
    linarith

/-- Two continuous paths joining opposite sides of a closed rectangle intersect.
No simplicity, genericity, or nondegeneracy of the rectangle is required. -/
theorem pathRectangle_crossing_intersection
    {a b : ℝ × ℝ} {p₀ p₁ q₀ q₁ : ℝ × ℝ}
    (P : Path p₀ p₁) (Q : Path q₀ q₁)
    (hPbox : ∀ t, a.1 ≤ (P t).1 ∧ (P t).1 ≤ b.1 ∧
      a.2 ≤ (P t).2 ∧ (P t).2 ≤ b.2)
    (hQbox : ∀ t, a.1 ≤ (Q t).1 ∧ (Q t).1 ≤ b.1 ∧
      a.2 ≤ (Q t).2 ∧ (Q t).2 ≤ b.2)
    (hPleft : (P 0).1 = a.1) (hPright : (P 1).1 = b.1)
    (hQbottom : (Q 0).2 = a.2) (hQtop : (Q 1).2 = b.2) :
    ∃ s t : I, P s = Q t := by
  let K : Set (ℝ × ℝ) := Set.Icc (0, 0) (1, 1)
  let fstI : C(K, I) := ⟨fun z => ⟨z.1.1, by
      have hz := z.property
      change (0, 0) ≤ (z : ℝ × ℝ) ∧ (z : ℝ × ℝ) ≤ (1, 1) at hz
      exact ⟨hz.1.1, hz.2.1⟩⟩,
    Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) (by
      intro z
      have hz := z.property
      change (0, 0) ≤ (z : ℝ × ℝ) ∧ (z : ℝ × ℝ) ≤ (1, 1) at hz
      exact ⟨hz.1.1, hz.2.1⟩)⟩
  let sndI : C(K, I) := ⟨fun z => ⟨z.1.2, by
      have hz := z.property
      change (0, 0) ≤ (z : ℝ × ℝ) ∧ (z : ℝ × ℝ) ≤ (1, 1) at hz
      exact ⟨hz.1.2, hz.2.2⟩⟩,
    Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) (by
      intro z
      have hz := z.property
      change (0, 0) ≤ (z : ℝ × ℝ) ∧ (z : ℝ × ℝ) ≤ (1, 1) at hz
      exact ⟨hz.1.2, hz.2.2⟩)⟩
  let ι : C(K, I × I) := fstI.prodMk sndI
  let f₁ : C(K, ℝ) := ⟨fun z => (P (ι z).1).1 - (Q (ι z).2).1, by fun_prop⟩
  let f₂ : C(K, ℝ) := ⟨fun z => (Q (ι z).2).2 - (P (ι z).1).2, by fun_prop⟩
  have hclamp : Continuous unitClamp := continuous_unitClamp
  let T : C(K, K) :=
    ⟨fun z => ⟨(unitClamp (z.1.1 - f₁ z), unitClamp (z.1.2 - f₂ z)), by
      change (0, 0) ≤ (unitClamp (z.1.1 - f₁ z), unitClamp (z.1.2 - f₂ z)) ∧
        (unitClamp (z.1.1 - f₁ z), unitClamp (z.1.2 - f₂ z)) ≤ (1, 1)
      exact ⟨⟨(unitClamp_mem _).1, (unitClamp_mem _).1⟩,
        ⟨(unitClamp_mem _).2, (unitClamp_mem _).2⟩⟩⟩,
      by fun_prop⟩
  obtain ⟨z, hzfix⟩ := brouwer_fixed_point K (convex_Icc (0, 0) (1, 1))
    isCompact_Icc ⟨(0, 0), by norm_num [K]⟩ T
  have hzcoord : (unitClamp (z.1.1 - f₁ z), unitClamp (z.1.2 - f₂ z)) = z.1 := by
    exact congrArg Subtype.val hzfix
  have hf₁ : f₁ z = 0 := by
    apply unitClamp_fixed_zero_of_signs z.1.1 (f₁ z) (ι z).1.property
      (congrArg Prod.fst hzcoord)
    · intro hs
      have hs' : (ι z).1 = 0 := Subtype.ext hs
      change (P (ι z).1).1 - (Q (ι z).2).1 ≤ 0
      have hp0 : P (ι z).1 = p₀ := by simp [hs']
      rw [hp0]
      have hq := (hQbox (ι z).2).1
      have hsrc : p₀.1 = a.1 := by
        have hpath : (P 0).1 = p₀.1 := congrArg Prod.fst P.source'
        linarith
      linarith
    · intro hs
      have hs' : (ι z).1 = 1 := Subtype.ext hs
      change 0 ≤ (P (ι z).1).1 - (Q (ι z).2).1
      have hp1 : P (ι z).1 = p₁ := by simp [hs']
      rw [hp1]
      have hq := (hQbox (ι z).2).2.1
      have htarget : p₁.1 = b.1 := by
        have hpath : (P 1).1 = p₁.1 := congrArg Prod.fst P.target'
        linarith
      linarith
  have hf₂ : f₂ z = 0 := by
    apply unitClamp_fixed_zero_of_signs z.1.2 (f₂ z) (ι z).2.property
      (congrArg Prod.snd hzcoord)
    · intro ht
      have ht' : (ι z).2 = 0 := Subtype.ext ht
      change (Q (ι z).2).2 - (P (ι z).1).2 ≤ 0
      have hq0 : Q (ι z).2 = q₀ := by simp [ht']
      rw [hq0]
      have hp := (hPbox (ι z).1).2.2.1
      have hsrc : q₀.2 = a.2 := by
        have hpath : (Q 0).2 = q₀.2 := congrArg Prod.snd Q.source'
        linarith
      linarith
    · intro ht
      have ht' : (ι z).2 = 1 := Subtype.ext ht
      change 0 ≤ (Q (ι z).2).2 - (P (ι z).1).2
      have hq1 : Q (ι z).2 = q₁ := by simp [ht']
      rw [hq1]
      have hp := (hPbox (ι z).1).2.2.2
      have htarget : q₁.2 = b.2 := by
        have hpath : (Q 1).2 = q₁.2 := congrArg Prod.snd Q.target'
        linarith
      linarith
  refine ⟨(ι z).1, (ι z).2, ?_⟩
  apply Prod.ext
  · have := congrArg (fun x : ℝ => x) hf₁
    dsimp [f₁] at this
    exact sub_eq_zero.mp this
  · have := congrArg (fun x : ℝ => x) hf₂
    dsimp [f₂] at this
    exact (sub_eq_zero.mp this).symm

end

end PottsDiscontinuity.FK.Curves
