module

public import PottsDiscontinuity.TorusCrossing.Exclusion
public import PottsDiscontinuity.TorusCrossing.Cut
public import PottsDiscontinuity.Duality.FiniteGraphBoundaryParity

/-!
# Existence: a missing primal connection forces a dual connection

If two primal cells joined by a closed edge `m` are not connected (rows wired), the dual
endpoints of `m` are connected in the complementary dual configuration (side columns wired).
The proof applies the handshake lemma to the dual graph of the cut edges of the primal component
of one endpoint.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (R : Rect)

/-- Dual graph with the edges carried by `E ⊆ inner`. -/
noncomputable abbrev dualOf (E : Finset Cell) : SimpleGraph R.dcells :=
  endGraph dualEnds R.dcells E

theorem dData_mono {E : Finset Cell} (hE : E ⊆ R.inner) : EndData dualEnds R.dcells E where
  mem m hm := R.dData.mem m (hE hm)
  ne := R.dData.ne
  inj := R.dData.inj

/-- Degree of an odd cell in the dual graph of `E`: the number of corners lying in `E`. -/
theorem dualOf_degree {E : Finset Cell} (hE : E ⊆ R.inner) (z : R.dcells) :
    (R.dualOf E).degree z = (E.filter (fun m => m ∈ corners z.1)).card := by
  have hz : ¬ IsPrimal z.1 := (mem_dcells.1 z.2).2
  rw [degree_eq (R.dData_mono hE)]
  congr 1
  apply Finset.filter_congr
  intro m _
  exact mem_dualEnds_iff z.1 m hz

/-- **Handshake for the dual graph.** -/
theorem dual_reachable_of_odd {E : Finset Cell} (hE : E ⊆ R.inner) (B T : Finset R.dcells)
    (hdisj : Disjoint B T)
    (heven : ∀ z : R.dcells, z ∉ B → z ∉ T → Even (E.filter (fun m => m ∈ corners z.1)).card)
    (hodd : Odd (∑ z ∈ B, (E.filter (fun m => m ∈ corners z.1)).card)) :
    ∃ b ∈ B, ∃ t ∈ T, (R.dualOf E).Reachable b t := by
  apply FK.exists_reachable_between_of_odd_degree_sum (R.dualOf E) B T hdisj
  · intro v hv
    rw [dualOf_degree R hE]
    exact heven v (fun h => hv (Finset.mem_union_left _ h)) (fun h => hv (Finset.mem_union_right _ h))
  · simpa only [dualOf_degree R hE] using hodd

/-- Reachability in `dualOf E` implies the component relation of any larger configuration. -/
theorem dualOf_reachable_le {E D : Finset Cell} (hED : E ⊆ D) (hD : D ⊆ R.inner)
    (ξ : FK.BoundaryCondition R.dcells) {x y : R.dcells} (h : (R.dualOf E).Reachable x y) :
    (FK.componentSetoid R.dG ξ (cfgOf R.dData D)).r x y := by
  have hle : (R.dualOf E).reachableSetoid ≤ FK.componentSetoid R.dG ξ (cfgOf R.dData D) := by
    apply FK.reachableSetoid_le_of_adj
    intro a b hab
    rw [dualOf, endGraph_adj] at hab
    apply FK.actualConnected_component
    apply FK.actualConnected_of_adj
    rw [openGraph_adj_iff R.dData, openMedials_cfgOf R.dData D hD]
    rcases hab.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · exact ⟨m, hED hm, Or.inl h⟩
    · exact ⟨m, hED hm, Or.inr h⟩
  exact hle h


/-- The cells of the primal component of `u` (as a predicate on all cells). -/
def compPred (A : Finset Cell) (u : R.pcells) (c : Cell) : Prop :=
  ∃ hc : c ∈ R.pcells, (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r ⟨c, hc⟩ u

/-- The cut edges of the board for a vertex predicate. -/
noncomputable def cutSet (X : Cell → Prop) : Finset Cell := R.inner.filter (IsCut X)

theorem mem_cutSet {X : Cell → Prop} {m : Cell} : m ∈ R.cutSet X ↔ m ∈ R.inner ∧ IsCut X m := by
  unfold cutSet; simp [Finset.mem_filter]

theorem compPred_iff {A : Finset Cell} {u : R.pcells} {x y : R.pcells}
    (hxy : (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r x y) :
    R.compPred A u x.1 ↔ R.compPred A u y.1 := by
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨y.2, (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).trans
      ((FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).symm hxy) h⟩
  · rintro ⟨hc, h⟩
    exact ⟨x.2, (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).trans hxy h⟩

/-- Open edges are never cut by a component predicate. -/
theorem not_cut_of_mem {A : Finset Cell} (hA : A ⊆ R.inner) (u : R.pcells) {m : Cell}
    (hm : m ∈ A) : ¬ IsCut (R.compPred A u) m := by
  intro hcut
  unfold IsCut at hcut
  have hmi := hA hm
  have hmem := R.pData.mem m hmi
  apply hcut
  have hadj : (FK.openGraph R.pG (cfgOf R.pData A)).Adj ⟨(primalEnds m).1, hmem.1⟩
      ⟨(primalEnds m).2, hmem.2⟩ := by
    rw [openGraph_adj_iff R.pData, openMedials_cfgOf R.pData A hA]
    exact ⟨m, hm, Or.inl rfl⟩
  have hrel := FK.actualConnected_component R.pG R.sepBC (cfgOf R.pData A)
    (FK.actualConnected_of_adj R.pG _ hadj)
  exact propext (R.compPred_iff hrel)

/-- Cells of the bottom row are related by the wiring. -/
theorem bottom_related (A : Finset Cell) {x y : R.pcells} (hx : x.1.2 = R.y0) (hy : y.1.2 = R.y0) :
    (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r x y :=
  FK.boundary_component R.pG R.sepBC _ (Or.inr (Or.inl ⟨hx, hy⟩))

theorem top_related (A : Finset Cell) {x y : R.pcells} (hx : x.1.2 = R.y0 + R.h)
    (hy : y.1.2 = R.y0 + R.h) :
    (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r x y :=
  FK.boundary_component R.pG R.sepBC _ (Or.inr (Or.inr ⟨hx, hy⟩))


theorem cutSet_filter_corners (X : Cell → Prop) (z : Cell) :
    (R.cutSet X).filter (fun m => m ∈ corners z) =
      (corners z).filter (fun m => m ∈ R.inner ∧ IsCut X m) := by
  ext m
  simp only [mem_cutSet, Finset.mem_filter]
  tauto

theorem outer_pcells (z : R.dcells) (hx1 : R.x0 < z.1.1) (hx2 : z.1.1 < R.x0 + R.w) :
    (z.1.1 - 1, z.1.2) ∈ R.pcells ∧ (z.1.1 + 1, z.1.2) ∈ R.pcells := by
  have hz := mem_dcells.1 z.2
  rw [mem_cells] at hz
  unfold IsPrimal at hz
  constructor <;> rw [mem_pcells, mem_cells] <;> unfold IsPrimal <;> dsimp only <;> omega

theorem compPred_cutSet_even (hh : 0 < R.h) (A : Finset Cell) (u : R.pcells) (z : R.dcells)
    (hx1 : R.x0 < z.1.1) (hx2 : z.1.1 < R.x0 + R.w) :
    Even ((R.cutSet (R.compPred A u)).filter (fun m => m ∈ corners z.1)).card := by
  rw [cutSet_filter_corners]
  have hz := mem_dcells.1 z.2
  have hzc := mem_cells.1 hz.1
  obtain ⟨hW, hE⟩ := R.outer_pcells z hx1 hx2
  apply cut_deg_even R hh _ z.1 hz.2 hx1 hx2 hzc.2.2.1 hzc.2.2.2
  · intro hb
    exact R.compPred_iff (u := u) (x := ⟨_, hW⟩) (y := ⟨_, hE⟩)
      (R.bottom_related A (by exact hb) (by exact hb))
  · intro ht
    exact R.compPred_iff (u := u) (x := ⟨_, hW⟩) (y := ⟨_, hE⟩)
      (R.top_related A (by exact ht) (by exact ht))


/-- **Existence.**  If two primal cells joined by a closed edge `m₀` are not connected (rows
wired), then the dual endpoints of `m₀` are connected in the complementary dual configuration
(side columns wired). -/
theorem existence (hh : 0 < R.h) (A : Finset Cell) (hA : A ⊆ R.inner) (m₀ : Cell)
    (hm₀ : m₀ ∈ R.inner) (u v : R.pcells) (hu : u.1 = (primalEnds m₀).1)
    (hv : v.1 = (primalEnds m₀).2) (u' v' : R.dcells) (hu' : u'.1 = (dualEnds m₀).1)
    (hv' : v'.1 = (dualEnds m₀).2)
    (hnot : ¬ (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r u v) :
    (FK.componentSetoid R.dG R.dualBC (cfgOf R.dData (R.inner \ insert m₀ A))).r u' v' := by
  set X := R.compPred A u with hX
  set E := R.cutSet X with hE
  set E' := E.erase m₀ with hE'
  set D := R.inner \ insert m₀ A with hD
  set sD := FK.componentSetoid R.dG R.dualBC (cfgOf R.dData D) with hsD
  have hDsub : D ⊆ R.inner := Finset.sdiff_subset
  have hEsub : E ⊆ R.inner := fun m hm => (R.mem_cutSet.1 hm).1
  have hm₀E : m₀ ∈ E := by
    rw [hE, mem_cutSet]
    refine ⟨hm₀, ?_⟩
    unfold IsCut
    have h1 : X (primalEnds m₀).1 := by
      refine ⟨by rw [← hu]; exact u.2, ?_⟩
      have : (⟨(primalEnds m₀).1, by rw [← hu]; exact u.2⟩ : R.pcells) = u := Subtype.ext hu.symm
      rw [this]
    have h2 : ¬ X (primalEnds m₀).2 := by
      rintro ⟨hc, h⟩
      apply hnot
      have : (⟨(primalEnds m₀).2, hc⟩ : R.pcells) = v := Subtype.ext hv.symm
      rw [this] at h
      exact (FK.componentSetoid R.pG R.sepBC _).symm h
    intro heq
    exact h2 (heq ▸ h1)
  have hE'sub : E' ⊆ D := by
    intro m hm
    rw [hE', Finset.mem_erase] at hm
    rw [hD, Finset.mem_sdiff, Finset.mem_insert, not_or]
    refine ⟨hEsub hm.2, hm.1, fun hmA => ?_⟩
    exact R.not_cut_of_mem hA u hmA (R.mem_cutSet.1 hm.2).2
  have hE'sub' : E' ⊆ R.inner := hE'sub.trans hDsub
  -- parity of the remaining cut edges at the interior odd cells
  have hpar : ∀ z : R.dcells, R.x0 < z.1.1 → z.1.1 < R.x0 + R.w →
      ((z = u' ∨ z = v') → Odd (E'.filter (fun m => m ∈ corners z.1)).card) ∧
      (¬ (z = u' ∨ z = v') → Even (E'.filter (fun m => m ∈ corners z.1)).card) := by
    intro z hx1 hx2
    have hev : Even (E.filter (fun m => m ∈ corners z.1)).card :=
      R.compPred_cutSet_even hh A u z hx1 hx2
    have hzprim : ¬ IsPrimal z.1 := (mem_dcells.1 z.2).2
    have hiff : m₀ ∈ corners z.1 ↔ (z = u' ∨ z = v') := by
      rw [← mem_dualEnds_iff z.1 m₀ hzprim]
      constructor
      · rintro (h | h)
        · left; exact Subtype.ext (by rw [h, hu'])
        · right; exact Subtype.ext (by rw [h, hv'])
      · rintro (h | h)
        · left; rw [h, hu']
        · right; rw [h, hv']
    have hfe : E'.filter (fun m => m ∈ corners z.1) = (E.filter (fun m => m ∈ corners z.1)).erase m₀ := by
      rw [hE']; exact Finset.filter_erase _ _ _
    rw [hfe]
    constructor
    · intro hz
      have hmem : m₀ ∈ E.filter (fun m => m ∈ corners z.1) :=
        Finset.mem_filter.2 ⟨hm₀E, hiff.2 hz⟩
      rw [Finset.card_erase_of_mem hmem]
      have hpos : 0 < (E.filter (fun m => m ∈ corners z.1)).card := Finset.card_pos.2 ⟨m₀, hmem⟩
      obtain ⟨k, hk⟩ := hev
      exact ⟨k - 1, by omega⟩
    · intro hz
      rw [Finset.erase_eq_of_notMem]
      · exact hev
      · intro hm; exact hz (hiff.1 (Finset.mem_filter.1 hm).2)
  -- wiring of the side columns
  have hLR : ∀ a b : R.dcells, (a.1.1 = R.x0 ∨ a.1.1 = R.x0 + R.w) →
      (b.1.1 = R.x0 ∨ b.1.1 = R.x0 + R.w) → sD.r a b := fun a b ha hb =>
    FK.boundary_component R.dG R.dualBC _ (Or.inr ⟨ha, hb⟩)
  have hreach : ∀ a b : R.dcells, (R.dualOf E').Reachable a b → sD.r a b := fun a b h =>
    R.dualOf_reachable_le hE'sub hDsub R.dualBC h
  have hne' : u' ≠ v' := fun h => dualEnds_ne m₀ (by rw [← hu', ← hv', h])
  -- the key step: an odd dual endpoint strictly inside reaches the side columns or its partner
  have key : ∀ a o : R.dcells, (a = u' ∧ o = v' ∨ a = v' ∧ o = u') → a.1.1 ≠ R.x0 →
      a.1.1 ≠ R.x0 + R.w →
      ∃ t : R.dcells, (t.1.1 = R.x0 ∨ t.1.1 = R.x0 + R.w ∨ t = o) ∧ (R.dualOf E').Reachable a t := by
    intro a o hao ha1 ha2
    have hac := mem_cells.1 (mem_dcells.1 a.2).1
    obtain ⟨hodd, hpo⟩ := hpar a (by omega) (by omega)
    have hao' : a ≠ o := by
      rcases hao with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hne'
      · rw [h1, h2]; exact hne'.symm
    have hao'' : a = u' ∨ a = v' := by
      rcases hao with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr h1
    obtain ⟨b, hb, t, ht, hr⟩ := R.dual_reachable_of_odd hE'sub'
      {a} (Finset.univ.filter (fun t : R.dcells => t.1.1 = R.x0 ∨ t.1.1 = R.x0 + R.w ∨ t = o))
      (by
        rw [Finset.disjoint_singleton_left]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or]
        exact ⟨ha1, ha2, hao'⟩)
      (by
        intro z hz1 hz2
        simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hz1 hz2
        have hzc := mem_cells.1 (mem_dcells.1 z.2).1
        refine (hpar z (by omega) (by omega)).2 ?_
        rintro (h | h)
        · rcases hao with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hz1 (h.trans h1.symm)
          · exact hz2.2.2 (h.trans h2.symm)
        · rcases hao with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hz2.2.2 (h.trans h2.symm)
          · exact hz1 (h.trans h1.symm)
      )
      (by
        rw [Finset.sum_singleton]
        exact hodd hao'')
    rw [Finset.mem_singleton] at hb
    subst hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact ⟨t, ht, hr⟩
  -- assemble
  by_cases hu1 : u'.1.1 = R.x0 ∨ u'.1.1 = R.x0 + R.w <;>
    by_cases hv1 : v'.1.1 = R.x0 ∨ v'.1.1 = R.x0 + R.w
  · exact hLR u' v' hu1 hv1
  · obtain ⟨t, ht, hr⟩ := key v' u' (Or.inr ⟨rfl, rfl⟩) (by tauto) (by tauto)
    have hr' := hreach _ _ hr
    rcases ht with ht | ht | ht
    · exact sD.symm (sD.trans hr' (hLR t u' (Or.inl ht) hu1))
    · exact sD.symm (sD.trans hr' (hLR t u' (Or.inr ht) hu1))
    · subst ht; exact sD.symm hr'
  · obtain ⟨t, ht, hr⟩ := key u' v' (Or.inl ⟨rfl, rfl⟩) (by tauto) (by tauto)
    have hr' := hreach _ _ hr
    rcases ht with ht | ht | ht
    · exact sD.trans hr' (hLR t v' (Or.inl ht) hv1)
    · exact sD.trans hr' (hLR t v' (Or.inr ht) hv1)
    · subst ht; exact hr'
  · obtain ⟨t₁, ht₁, hr₁⟩ := key u' v' (Or.inl ⟨rfl, rfl⟩) (by tauto) (by tauto)
    obtain ⟨t₂, ht₂, hr₂⟩ := key v' u' (Or.inr ⟨rfl, rfl⟩) (by tauto) (by tauto)
    have h1 := hreach _ _ hr₁
    have h2 := hreach _ _ hr₂
    by_cases e1 : t₁ = v'
    · subst e1; exact h1
    · by_cases e2 : t₂ = u'
      · subst e2; exact sD.symm h2
      · have l1 : t₁.1.1 = R.x0 ∨ t₁.1.1 = R.x0 + R.w := by
          rcases ht₁ with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h e1
        have l2 : t₂.1.1 = R.x0 ∨ t₂.1.1 = R.x0 + R.w := by
          rcases ht₂ with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h e2
        exact sD.trans h1 (sD.trans (hLR _ _ l1 l2) (sD.symm h2))

end Rect

end PottsDiscontinuity.TorusCrossing
