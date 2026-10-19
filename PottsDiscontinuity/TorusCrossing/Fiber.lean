module

public import PottsDiscontinuity.TorusCrossing.SubGraph
public import PottsDiscontinuity.TorusCrossing.Square

/-!
# The conditional crossing bound given the two explorations

Conditionally on the state of all explored edges of the two explorations (a *fiber*), the
probability of a crossing from the lower boundary to the upper boundary is at least the
mixed-boundary square crossing probability.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable {Q : Rect} {bB bT : ℕ}

/-- The crossing event used by the fibre argument: an open path from a cell of the rows
`≤ y0 + bB - 1` to a cell of the rows `≥ y0 + h - bT + 1`. -/
def crossEv (Q : Rect) (bB bT : ℕ) (A : Finset Cell) : Prop :=
  ∃ u v : Cell, u.2 ≤ Q.y0 + bB - 1 ∧ Q.y0 + Q.h - bT + 1 ≤ v.2 ∧
    Relation.ReflTransGen (StepRel primalEnds A) u v

theorem extend_low {A₀ A : Finset Cell} (hbdA : Q.bdB bB A₀ ⊆ A) {x : Cell}
    (hx : Vtx (Q.bdB bB A₀) x) :
    ∃ u : Cell, u.2 ≤ Q.y0 + bB - 1 ∧ Relation.ReflTransGen (StepRel primalEnds A) u x := by
  obtain ⟨e, he, hxe⟩ := hx
  have hein : e ∈ (Q.botB bB).inner := ((Q.botB bB).mem_expBd_iff.1 he).1
  have hr := Rect.mem_inner.1 hein
  simp only [botB_x0, botB_y0, botB_w, botB_h] at hr
  have hstep : StepRel primalEnds A (primalEnds e).2 (primalEnds e).1 :=
    stepRel_symm (step_of_mem (hbdA he))
  have hlow : (primalEnds e).2.2 ≤ Q.y0 + bB - 1 := by
    rw [primalEnds_snd_row]; omega
  rcases hxe with rfl | rfl
  · exact ⟨(primalEnds e).2, hlow, Relation.ReflTransGen.single hstep⟩
  · exact ⟨_, hlow, Relation.ReflTransGen.refl⟩

theorem extend_up {A₀ A : Finset Cell} (hbdA : Q.bdT bT A₀ ⊆ A) {y : Cell}
    (hy : Vtx (Q.bdT bT A₀) y) :
    ∃ v : Cell, Q.y0 + Q.h - bT + 1 ≤ v.2 ∧ Relation.ReflTransGen (StepRel primalEnds A) y v := by
  obtain ⟨e, he, hye⟩ := hy
  have hein : e ∈ (Q.topT bT).inner := ((Q.topT bT).mem_expBd_iff.1 he).1
  have hr := Rect.mem_inner.1 hein
  simp only [topT_x0, topT_y0, topT_w, topT_h] at hr
  have hstep : StepRel primalEnds A (primalEnds e).2 (primalEnds e).1 :=
    stepRel_symm (step_of_mem (hbdA he))
  have hup : Q.y0 + Q.h - bT + 1 ≤ (primalEnds e).1.2 := by
    rw [primalEnds_fst_row]; omega
  rcases hye with rfl | rfl
  · exact ⟨_, hup, Relation.ReflTransGen.refl⟩
  · exact ⟨(primalEnds e).1, hup, Relation.ReflTransGen.single hstep⟩

theorem crossEv_of_success {A₀ A : Finset Cell} (hbdB : Q.bdB bB A₀ ⊆ A) (hbdT : Q.bdT bT A₀ ⊆ A)
    (hD : (A ∩ Q.unx (Q.exAll bB bT A₀)) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀ ⊆ A)
    (hs : ∃ x y, Vtx (Q.bdB bB A₀) x ∧ Vtx (Q.bdT bT A₀) y ∧
      Relation.ReflTransGen (StepRel primalEnds
        ((A ∩ Q.unx (Q.exAll bB bT A₀)) ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀)) x y) :
    Q.crossEv bB bT A := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hs
  obtain ⟨u, hu, hux⟩ := extend_low hbdB hx
  obtain ⟨v, hv, hyv⟩ := extend_up hbdT hy
  have hxy' : Relation.ReflTransGen (StepRel primalEnds A) x y :=
    Relation.ReflTransGen.mono (fun a b hab => stepRel_mono hD hab) x y hxy
  exact ⟨u, v, hu, hv, Relation.ReflTransGen.trans (Relation.ReflTransGen.trans hux hxy') hyv⟩


theorem comp_of_path (ξ : FK.BoundaryCondition Q.pcells) {H₀ S : Finset Cell}
    (hH : H₀ ⊆ Q.inner) (hS : S ⊆ H₀) {x y : Q.pcells}
    (h : Relation.ReflTransGen (StepRel primalEnds S) x.1 y.1) :
    (FK.componentSetoid Q.pG ξ (cfgOf Q.pData H₀)).r x y := by
  apply FK.actualConnected_component
  rw [actualConnected_iff Q.pData, openMedials_cfgOf Q.pData H₀ hH]
  exact Relation.ReflTransGen.mono (fun a b hab => stepRel_mono hS hab) x.1 y.1 h

attribute [local instance] FK.configurationMeasurableSpace

/-- **Conditional crossing bound on a fibre.** -/
theorem fiber_bound (q : Set.Ici (1 : ℝ)) (hg : Q.Geo bB bT)
    (η : FK.BoundaryCondition Q.pcells) {A₀ : Finset Cell}
    (hbar : Q.barAll bB bT A₀) :
    (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal *
      (FK.measure Q.pG (critParams q) η
        {C | openMedials Q.pData C ∩ Q.exAll bB bT A₀ = A₀ ∩ Q.exAll bB bT A₀}).toReal ≤
    (FK.measure Q.pG (critParams q) η
        {C | openMedials Q.pData C ∩ Q.exAll bB bT A₀ = A₀ ∩ Q.exAll bB bT A₀ ∧
          Q.crossEv bB bT (openMedials Q.pData C)}).toReal := by
  set EX := Q.exAll bB bT A₀ with hEXd
  have hEXin : EX ⊆ Q.inner := exAll_subset_inner A₀ hg
  set H₀ := A₀ ∩ EX with hH₀
  have hHsub : H₀ ⊆ EX := Finset.inter_subset_right
  have hBDB_EX : Q.bdB bB A₀ ⊆ EX := (bdB_subset_exB Q bB A₀).trans Finset.subset_union_left
  have hBDT_EX : Q.bdT bT A₀ ⊆ EX := (bdT_subset_exT Q bT A₀).trans Finset.subset_union_right
  have hBDB_H : Q.bdB bB A₀ ⊆ H₀ :=
    Finset.subset_inter ((Q.botB bB).expBd_subset _ _ A₀) hBDB_EX
  have hBDT_H : Q.bdT bT A₀ ⊆ H₀ :=
    Finset.subset_inter ((Q.topT bT).expBd_subset _ _ A₀) hBDT_EX
  have hHin : H₀ ⊆ Q.inner := hHsub.trans hEXin
  let 𝒮 : Set (Finset Cell) := {A' | ∃ x y, Vtx (Q.bdB bB A₀) x ∧ Vtx (Q.bdT bT A₀) y ∧
    Relation.ReflTransGen (StepRel primalEnds (A' ∪ Q.bdB bB A₀ ∪ Q.bdT bT A₀)) x y}
  have h𝒮 : ∀ A B : Finset Cell, A ⊆ B → A ∈ 𝒮 → B ∈ 𝒮 := by
    rintro A B hAB ⟨x, y, hx, hy, hxy⟩
    refine ⟨x, y, hx, hy, ?_⟩
    exact Relation.ReflTransGen.mono (fun a b hab => stepRel_mono (by
      intro m hm
      rcases Finset.mem_union.1 hm with h | h
      · rcases Finset.mem_union.1 h with h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hAB h))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      · exact Finset.mem_union_right _ h) hab) x y hxy
  set θ := critParams q with hθ
  -- (1) the fibre together with the event 𝒮 forces the crossing
  have hsub : {C | openMedials Q.pData C ∩ EX = H₀ ∧ openMedials Q.pData C ∩ Q.unx EX ∈ 𝒮} ⊆
      {C | openMedials Q.pData C ∩ EX = H₀ ∧ Q.crossEv bB bT (openMedials Q.pData C)} := by
    rintro C ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have hH : H₀ ⊆ openMedials Q.pData C := by
      rw [← h1]; exact Finset.inter_subset_left
    refine crossEv_of_success (hBDB_H.trans hH) (hBDT_H.trans hH) ?_ h2
    intro m hm
    rcases Finset.mem_union.1 hm with h | h
    · rcases Finset.mem_union.1 h with h | h
      · exact (Finset.mem_inter.1 h).1
      · exact (hBDB_H.trans hH) h
    · exact (hBDT_H.trans hH) h
  have h1 : (FK.measure Q.pG θ η {C | openMedials Q.pData C ∩ EX = H₀ ∧
      openMedials Q.pData C ∩ Q.unx EX ∈ 𝒮}).toReal ≤
      (FK.measure Q.pG θ η {C | openMedials Q.pData C ∩ EX = H₀ ∧
        Q.crossEv bB bT (openMedials Q.pData C)}).toReal :=
    ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_mono hsub)
  -- (2) the Markov identity
  rw [markov_cell θ η hEXin hHsub 𝒮, ENNReal.toReal_mul] at h1
  -- (3) comparison of the induced partitions
  set Pψ := FK.componentSetoid Q.pG Q.sepBC (cfgOf Q.pData EX) with hPψ
  set Pη := FK.componentSetoid Q.pG η (cfgOf Q.pData H₀) with hPη
  have hPP : ∀ x y : Q.pcells, Vtx (Q.unx EX) x.1 → Vtx (Q.unx EX) y.1 → Pψ.r x y → Pη.r x y := by
    intro x y hx hy hxy
    rcases kc hg hbar hx hy hxy with h | ⟨hxB, hyB⟩ | ⟨hxT, hyT⟩
    · subst h; exact Setoid.refl' _ _
    · exact comp_of_path η hHin hBDB_H (Vtx_bdB_connected hg hbar.1 hxB hyB)
    · exact comp_of_path η hHin hBDT_H (Vtx_bdT_connected hg hbar.2 hxT hyT)
  have h2 := nu_mono (Q := Q) (Ex := EX) θ hPP h𝒮
  -- (4) the comparison with the square measure, conditioned on all explored edges open
  have hfrozS := markov_cell θ Q.sepBC hEXin (subset_refl EX) 𝒮
  have hA_in : ∀ C : FK.Configuration Q.pG, openMedials Q.pData C ⊆ Q.inner :=
    fun C => openMedials_subset Q.pData C
  have hevent : {C | EX ⊆ openMedials Q.pData C} ∩ Q.crossP ⊆
      {C | openMedials Q.pData C ∩ EX = EX ∧ openMedials Q.pData C ∩ Q.unx EX ∈ 𝒮} := by
    rintro C ⟨hC1, hC2⟩
    refine ⟨Finset.inter_eq_right.2 hC1, ?_⟩
    obtain ⟨u, v, hu, hv, huv⟩ := hC2
    rw [actualConnected_iff Q.pData] at huv
    obtain ⟨x, y, hx, hy, hxy⟩ := cross_to_success hg hbar (hA_in C) hu hv huv
    refine ⟨x, y, hx, hy, ?_⟩
    have : openMedials Q.pData C ∩ Q.unx EX = openMedials Q.pData C \ EX := by
      ext m
      simp only [Finset.mem_inter, Finset.mem_sdiff, mem_unx]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hA_in C h1, h3⟩
    rw [this]; exact hxy
  have hupper1 : IsUpperSet {C : FK.Configuration Q.pG | EX ⊆ openMedials Q.pData C} := by
    intro C C' hCC' hC
    exact hC.trans (openMedials_mono' hCC')
  have hFKG := FK.measure_positive_association (G := Q.pG) θ Q.sepBC _ _ hupper1
    Q.isUpperSet_crossP
  have hset_eq : {C : FK.Configuration Q.pG | openMedials Q.pData C ∩ EX = EX} =
      {C | EX ⊆ openMedials Q.pData C} := by
    ext C; simp [Finset.inter_eq_right]
  rw [hset_eq] at hfrozS
  have hpos : 0 < (FK.measure Q.pG θ Q.sepBC {C | EX ⊆ openMedials Q.pData C}).toReal := by
    apply ENNReal.toReal_pos
    · exact ((FK.measure_pos_iff _ _ _ _).2 ⟨Finset.univ, by
        intro m hm
        exact (mem_openMedials Q.pData _ m).2 ⟨hEXin hm, by simp⟩⟩).ne'
    · exact MeasureTheory.measure_ne_top _ _
  have h3 : (FK.measure Q.pG θ Q.sepBC ({C | EX ⊆ openMedials Q.pData C} ∩ Q.crossP)).toReal ≤
      (FK.measure Q.pG θ Q.sepBC {C | EX ⊆ openMedials Q.pData C ∧
        openMedials Q.pData C ∩ Q.unx EX ∈ 𝒮}).toReal := by
    apply ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
    apply MeasureTheory.measure_mono
    intro C hC
    have := hevent hC
    exact ⟨Finset.inter_eq_right.1 this.1, this.2⟩
  have hfrozS' : (FK.measure Q.pG θ Q.sepBC {C | EX ⊆ openMedials Q.pData C ∧
        openMedials Q.pData C ∩ Q.unx EX ∈ 𝒮}).toReal =
      (nuMeasure Q EX θ Pψ 𝒮).toReal *
        (FK.measure Q.pG θ Q.sepBC {C | EX ⊆ openMedials Q.pData C}).toReal := by
    have := congrArg ENNReal.toReal hfrozS
    rw [ENNReal.toReal_mul] at this
    convert this using 3
    ext C
    simp [Finset.inter_eq_right]
  have hκ : (FK.measure Q.pG θ Q.sepBC Q.crossP).toReal ≤ (nuMeasure Q EX θ Pψ 𝒮).toReal := by
    have h4 := hFKG
    nlinarith [h3, hfrozS']
  have hnn : 0 ≤ (FK.measure Q.pG θ η {C | openMedials Q.pData C ∩ EX = H₀}).toReal :=
    ENNReal.toReal_nonneg
  calc (FK.measure Q.pG θ Q.sepBC Q.crossP).toReal *
        (FK.measure Q.pG θ η {C | openMedials Q.pData C ∩ EX = H₀}).toReal
      ≤ (nuMeasure Q EX θ Pη 𝒮).toReal *
        (FK.measure Q.pG θ η {C | openMedials Q.pData C ∩ EX = H₀}).toReal :=
        mul_le_mul_of_nonneg_right (hκ.trans h2) hnn
    _ ≤ _ := h1

end Rect

/-- Summation over fibres of a function: a lower bound on every fibre of `E` gives the same bound
on `E`. -/
theorem sum_fibers {X β : Type*} [Fintype X] [DecidableEq β] [MeasurableSpace X]
    (hms : ∀ s : Set X, MeasurableSet s) (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (key : X → β) (E Y : Set X) (κ : ℝ)
    (hE : ∀ x ∈ E, ∀ x', key x' = key x → x' ∈ E)
    (hfib : ∀ x ∈ E, κ * μ.real {x' | key x' = key x} ≤ μ.real (Y ∩ {x' | key x' = key x})) :
    κ * μ.real E ≤ μ.real (Y ∩ E) := by
  set K : Finset β := (Finset.univ.filter (fun x => x ∈ E)).image key with hK
  have hKmem : ∀ k ∈ K, ∃ x ∈ E, key x = k := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨x, (Finset.mem_filter.1 hx).2, rfl⟩
  have hdisj : (↑K : Set β).PairwiseDisjoint (fun k => {x' : X | key x' = k}) := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    exact hab (hxa.symm.trans hxb)
  have hdisj' : (↑K : Set β).PairwiseDisjoint (fun k => Y ∩ {x' : X | key x' = k}) := by
    intro a ha b hb hab
    exact (hdisj ha hb hab).mono Set.inter_subset_right Set.inter_subset_right
  have hEdec : E = ⋃ k ∈ K, {x' : X | key x' = k} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hx
      exact ⟨key x, Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩, rfl⟩, rfl⟩
    · rintro ⟨k, hk, hxk⟩
      obtain ⟨x0, hx0, rfl⟩ := hKmem k hk
      exact hE x0 hx0 x hxk
  have hYdec : Y ∩ E = ⋃ k ∈ K, (Y ∩ {x' : X | key x' = k}) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨hY, hx⟩
      exact ⟨key x, Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩, rfl⟩,
        hY, rfl⟩
    · rintro ⟨k, hk, hY, hxk⟩
      obtain ⟨x0, hx0, rfl⟩ := hKmem k hk
      exact ⟨hY, hE x0 hx0 x hxk⟩
  have h1 : μ.real E = ∑ k ∈ K, μ.real {x' : X | key x' = k} := by
    conv_lhs => rw [hEdec]
    exact MeasureTheory.measureReal_biUnion_finset hdisj (fun k _ => hms _)
  have h2 : μ.real (Y ∩ E) = ∑ k ∈ K, μ.real (Y ∩ {x' : X | key x' = k}) := by
    conv_lhs => rw [hYdec]
    exact MeasureTheory.measureReal_biUnion_finset hdisj' (fun k _ => hms _)
  rw [h1, h2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  obtain ⟨x, hx, rfl⟩ := hKmem k hk
  exact hfib x hx

namespace Rect

variable {Q : Rect} {bB bT : ℕ}

attribute [local instance] FK.configurationMeasurableSpace

/-- **Board-level bound** ("BL"): for every boundary condition, the probability of the crossing
event is at least the mixed square crossing probability times the probability of the two
barriers. -/
theorem board_bl (q : Set.Ici (1 : ℝ)) (hg : Q.Geo bB bT)
    (η : FK.BoundaryCondition Q.pcells) :
    (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal *
      (FK.measure Q.pG (critParams q) η
        {C | Q.barAll bB bT (openMedials Q.pData C)}).toReal ≤
    (FK.measure Q.pG (critParams q) η
        {C | Q.crossEv bB bT (openMedials Q.pData C)}).toReal := by
  let : Fintype Q.pG.edgeSet := Fintype.ofFinite _
  have : MeasureTheory.IsFiniteMeasure (FK.measure Q.pG (critParams q) η) := inferInstance
  let key : FK.Configuration Q.pG → Finset Cell × Finset Cell := fun C =>
    (Q.exAll bB bT (openMedials Q.pData C),
      openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData C))
  have hfibre : ∀ x : FK.Configuration Q.pG, {x' | key x' = key x} =
      {C | openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData x) =
        openMedials Q.pData x ∩ Q.exAll bB bT (openMedials Q.pData x)} := by
    intro x
    ext x'
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [key] at h1 h2
      rw [h1] at h2
      exact h2
    · intro h
      have := exAll_congr (bB := bB) (bT := bT) (Q := Q) h
      simp only [key]
      rw [this.1, h]
  have key_main := sum_fibers (fun s => MeasurableSpace.measurableSet_top)
    (FK.measure Q.pG (critParams q) η) key
    {C | Q.barAll bB bT (openMedials Q.pData C)} {C | Q.crossEv bB bT (openMedials Q.pData C)}
    (FK.measure Q.pG (critParams q) Q.sepBC Q.crossP).toReal
    (by
      intro x hx x' hx'
      have hx'' : x' ∈ {x' | key x' = key x} := hx'
      rw [hfibre] at hx''
      have := exAll_congr (bB := bB) (bT := bT) (Q := Q) hx''
      exact ⟨this.2.2.2.2.2.1.2 hx.1, this.2.2.2.2.2.2.2 hx.2⟩)
    (by
      intro x hx
      rw [hfibre]
      have := fiber_bound q hg η hx
      have heq : {C : FK.Configuration Q.pG | Q.crossEv bB bT (openMedials Q.pData C)} ∩
          {C | openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData x) =
            openMedials Q.pData x ∩ Q.exAll bB bT (openMedials Q.pData x)} =
          {C | openMedials Q.pData C ∩ Q.exAll bB bT (openMedials Q.pData x) =
            openMedials Q.pData x ∩ Q.exAll bB bT (openMedials Q.pData x) ∧
            Q.crossEv bB bT (openMedials Q.pData C)} := by
        ext C; simp [and_comm]
      rw [heq]
      exact this)
  calc _ ≤ _ := key_main
    _ ≤ _ := ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_mono Set.inter_subset_left)

end Rect

end PottsDiscontinuity.TorusCrossing
