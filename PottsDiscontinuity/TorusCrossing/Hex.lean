module

public import PottsDiscontinuity.TorusCrossing.SelfDual

/-!
# Hex-type existence: no vertical primal crossing forces a horizontal dual crossing

The cut edges of the component of the bottom row, which contains no top cell, form a dual
subgraph in which every odd cell strictly between the side columns has even degree, while the
total degree over the left column is odd.  The handshake lemma then produces a dual path from
the left column to the right column.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (R : Rect)

/-- The primal cell of row `j` among the two leftmost columns. -/
def wcell (j : ℤ) : Cell := if IsPrimal (R.x0, j) then (R.x0, j) else (R.x0 + 1, j)

theorem wcell_primal (j : ℤ) : IsPrimal (R.wcell j) := by
  unfold wcell
  split_ifs with h
  · exact h
  · unfold IsPrimal at *; dsimp only at *; omega

theorem wcell_row (j : ℤ) : (R.wcell j).2 = j := by
  unfold wcell; split_ifs <;> rfl

theorem wcell_col (j : ℤ) : (R.wcell j).1 = R.x0 ∨ (R.wcell j).1 = R.x0 + 1 := by
  unfold wcell; split_ifs <;> simp

theorem primalEnds_leftcol (b : ℤ) : primalEnds (R.x0 + 1, b) = (R.wcell b, R.wcell (b - 1)) := by
  unfold wcell primalEnds
  simp only [IsPrimal]
  by_cases h : (R.x0 + b) % 2 = 0
  · have h0 : ¬ ((R.x0 + 1 + b) % 2 = 0) := by omega
    have h2 : ¬ ((R.x0 + (b - 1)) % 2 = 0) := by omega
    simp only [h, h0, h2, ite_true, ite_false, Prod.mk.injEq, and_true]
    omega
  · have h0 : ((R.x0 + 1 + b) % 2 = 0) := by omega
    have h2 : ((R.x0 + (b - 1)) % 2 = 0) := by omega
    simp only [h, h0, h2, ite_true, ite_false, Prod.mk.injEq, and_true, true_and]
    omega


/-- Odd cells of the left column. -/
noncomputable def leftFaces : Finset R.dcells := Finset.univ.filter (fun z => z.1.1 = R.x0)

/-- Odd cells of the right column. -/
noncomputable def rightFaces : Finset R.dcells :=
  Finset.univ.filter (fun z => z.1.1 = R.x0 + R.w)

theorem leftcol_filter (m : Cell) (hm : m ∈ R.inner) :
    (R.dcells.filter (fun c => c.1 = R.x0 ∧ m ∈ corners c)).card =
      if m.1 = R.x0 + 1 then 1 else 0 := by
  have hmi := mem_inner.1 hm
  by_cases h1 : m.1 = R.x0 + 1
  · rw [ite_eq_left h1, Finset.card_eq_one]
    by_cases hp : IsPrimal (R.x0, m.2)
    · refine ⟨(R.x0, m.2 - 1), ?_⟩
      ext c
      simp only [Finset.mem_filter, Finset.mem_singleton, mem_dcells, mem_cells, corners,
        Finset.mem_insert, Prod.ext_iff]
      unfold IsPrimal at *
      dsimp only at *
      omega
    · refine ⟨(R.x0, m.2), ?_⟩
      ext c
      simp only [Finset.mem_filter, Finset.mem_singleton, mem_dcells, mem_cells, corners,
        Finset.mem_insert, Prod.ext_iff]
      unfold IsPrimal at *
      dsimp only at *
      omega
  · rw [ite_eq_right h1, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hc
    simp only [corners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hc
    omega

/-- Sum over the left column of the dual degrees = number of edges of the first column. -/
theorem leftSum_eq (E : Finset Cell) (hE : E ⊆ R.inner) :
    ∑ z ∈ R.leftFaces, (E.filter (fun m => m ∈ corners z.1)).card =
      (E.filter (fun m => m.1 = R.x0 + 1)).card := by
  unfold leftFaces
  rw [Finset.sum_filter]
  have e1 : ∀ g : Cell → ℕ, ∑ z : R.dcells, (if z.1.1 = R.x0 then g z.1 else 0) =
      ∑ c ∈ R.dcells, (if c.1 = R.x0 then g c else 0) := fun g =>
    Finset.sum_coe_sort R.dcells (fun c => if c.1 = R.x0 then g c else 0)
  rw [e1 (fun c => (E.filter (fun m => m ∈ corners c)).card)]
  calc ∑ c ∈ R.dcells, (if c.1 = R.x0 then (E.filter (fun m => m ∈ corners c)).card else 0)
      = ∑ c ∈ R.dcells, ∑ m ∈ E, (if c.1 = R.x0 ∧ m ∈ corners c then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.card_filter]
        split_ifs with h
        · simp [h]
        · simp [h]
    _ = ∑ m ∈ E, ∑ c ∈ R.dcells, (if c.1 = R.x0 ∧ m ∈ corners c then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ m ∈ E, (if m.1 = R.x0 + 1 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [← R.leftcol_filter m (hE hm), Finset.card_filter]
    _ = (E.filter (fun m => m.1 = R.x0 + 1)).card := by rw [Finset.card_filter]


theorem isCut_leftcol (X : Cell → Prop) (b : ℤ) :
    IsCut X (R.x0 + 1, b) ↔ ¬ (X (R.wcell b) ↔ X (R.wcell (b - 1))) := by
  unfold IsCut
  rw [R.primalEnds_leftcol]
  dsimp only
  tauto

/-- Parity of the number of cut edges in the first column of medial vertices. -/
theorem cnt_parity (X : Cell → Prop) (k : ℕ) :
    Even ((Finset.Icc (R.y0 + 1) (R.y0 + k)).filter (fun b => IsCut X (R.x0 + 1, b))).card ↔
      (X (R.wcell R.y0) ↔ X (R.wcell (R.y0 + k))) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hset : Finset.Icc (R.y0 + 1) (R.y0 + ((k + 1 : ℕ) : ℤ)) =
        insert (R.y0 + ((k + 1 : ℕ) : ℤ)) (Finset.Icc (R.y0 + 1) (R.y0 + (k : ℤ))) := by
      ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hset, Finset.filter_insert]
    have hnot : R.y0 + ((k + 1 : ℕ) : ℤ) ∉
        (Finset.Icc (R.y0 + 1) (R.y0 + (k : ℤ))).filter (fun b => IsCut X (R.x0 + 1, b)) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]; push_cast; omega
    have hlast := R.isCut_leftcol X (R.y0 + ((k + 1 : ℕ) : ℤ))
    rw [show R.y0 + ((k + 1 : ℕ) : ℤ) - 1 = R.y0 + (k : ℤ) by push_cast; ring] at hlast
    by_cases hc : IsCut X (R.x0 + 1, R.y0 + ((k + 1 : ℕ) : ℤ))
    · rw [ite_eq_left hc, Finset.card_insert_of_notMem hnot, Nat.even_add_one, ih]
      have := hlast.1 hc
      by_cases h1 : X (R.wcell R.y0) <;> by_cases h2 : X (R.wcell (R.y0 + (k : ℤ))) <;>
        by_cases h3 : X (R.wcell (R.y0 + ((k + 1 : ℕ) : ℤ))) <;> simp_all
    · rw [ite_eq_right hc]
      have : (X (R.wcell (R.y0 + ((k + 1 : ℕ) : ℤ))) ↔ X (R.wcell (R.y0 + (k : ℤ)))) := by
        by_contra hn; exact hc (hlast.2 hn)
      rw [ih]
      by_cases h1 : X (R.wcell R.y0) <;> by_cases h2 : X (R.wcell (R.y0 + (k : ℤ))) <;>
        by_cases h3 : X (R.wcell (R.y0 + ((k + 1 : ℕ) : ℤ))) <;> simp_all


theorem cutSet_col_card (hw : 0 < R.w) (X : Cell → Prop) :
    ((R.cutSet X).filter (fun m => m.1 = R.x0 + 1)).card =
      ((Finset.Icc (R.y0 + 1) (R.y0 + (R.h : ℤ))).filter
        (fun b => IsCut X (R.x0 + 1, b))).card := by
  have hw' : (0 : ℤ) < R.w := by exact_mod_cast hw
  have : (R.cutSet X).filter (fun m => m.1 = R.x0 + 1) =
      ((Finset.Icc (R.y0 + 1) (R.y0 + (R.h : ℤ))).filter
        (fun b => IsCut X (R.x0 + 1, b))).image (fun b => (R.x0 + 1, b)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc, mem_cutSet, mem_inner]
    constructor
    · rintro ⟨⟨⟨h1, h2, h3, h4⟩, hc⟩, h5⟩
      exact ⟨m.2, ⟨⟨h3, h4⟩, by rw [← h5]; exact hc⟩, by rw [← h5]⟩
    · rintro ⟨b, ⟨⟨h3, h4⟩, hc⟩, rfl⟩
      exact ⟨⟨⟨by omega, by omega, h3, h4⟩, hc⟩, rfl⟩
  rw [this, Finset.card_image_of_injective]
  intro a b hab
  exact (Prod.ext_iff.1 hab).2

/-- The first column of cut edges has odd cardinality when the bottom corner is inside `X`
and the top corner is outside. -/
theorem cutSet_col_odd (hw : 0 < R.w) (X : Cell → Prop) (hbot : X (R.wcell R.y0))
    (htop : ¬ X (R.wcell (R.y0 + R.h))) :
    Odd ((R.cutSet X).filter (fun m => m.1 = R.x0 + 1)).card := by
  rw [R.cutSet_col_card hw X, ← Nat.not_even_iff_odd]
  intro hev
  have := (R.cnt_parity X R.h).1 hev
  exact htop (this.1 hbot)


/-- Reachability in the dual graph of `E` gives actual open connectivity for a larger set. -/
theorem dualOf_actualConnected {E D : Finset Cell} (hED : E ⊆ D) (hD : D ⊆ R.inner)
    {x y : R.dcells} (h : (R.dualOf E).Reachable x y) :
    FK.ActualConnected R.dG (cfgOf R.dData D) x y := by
  have hle : R.dualOf E ≤ FK.openGraph R.dG (cfgOf R.dData D) := by
    intro a b hab
    rw [dualOf, endGraph_adj] at hab
    rw [openGraph_adj_iff R.dData, openMedials_cfgOf R.dData D hD]
    rcases hab.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · exact ⟨m, hED hm, Or.inl h⟩
    · exact ⟨m, hED hm, Or.inr h⟩
  exact h.mono hle

/-- Cells connected to the bottom row by open paths. -/
def botComp (C : FK.Configuration R.pG) (c : Cell) : Prop :=
  ∃ hc : c ∈ R.pcells, ∃ b : R.pcells, b.1.2 = R.y0 ∧ FK.ActualConnected R.pG C b ⟨c, hc⟩

theorem botComp_of_adj (C : FK.Configuration R.pG) {x y : R.pcells}
    (hxy : (FK.openGraph R.pG C).Adj x y) : R.botComp C x.1 ↔ R.botComp C y.1 := by
  constructor
  · rintro ⟨_, b, hb, h⟩
    exact ⟨y.2, b, hb, h.trans (SimpleGraph.Adj.reachable hxy)⟩
  · rintro ⟨_, b, hb, h⟩
    exact ⟨x.2, b, hb, h.trans (SimpleGraph.Adj.reachable hxy.symm)⟩

theorem hex (hh : 0 < R.h) (hw : 0 < R.w) (C : FK.Configuration R.pG)
    (hno : ¬ ∃ u v : R.pcells, u.1.2 = R.y0 ∧ v.1.2 = R.y0 + R.h ∧
      FK.ActualConnected R.pG C u v) :
    ∃ z z' : R.dcells, z.1.1 = R.x0 ∧ z'.1.1 = R.x0 + R.w ∧
      FK.ActualConnected R.dG (R.dualEquiv C) z z' := by
  have hh' : (0 : ℤ) < R.h := by exact_mod_cast hh
  have hw' : (0 : ℤ) < R.w := by exact_mod_cast hw
  set A := openMedials R.pData C with hA
  have hAsub : A ⊆ R.inner := openMedials_subset R.pData C
  set X := R.botComp C with hX
  set E := R.cutSet X with hE
  have hEsub : E ⊆ R.inner := fun m hm => (R.mem_cutSet.1 hm).1
  have hEc : E ⊆ R.inner \ A := by
    intro m hm
    rw [Finset.mem_sdiff]
    refine ⟨hEsub hm, fun hmA => ?_⟩
    have hcut := (R.mem_cutSet.1 hm).2
    have hmem := R.pData.mem m (hAsub hmA)
    apply hcut
    have hadj : (FK.openGraph R.pG C).Adj ⟨(primalEnds m).1, hmem.1⟩ ⟨(primalEnds m).2, hmem.2⟩ := by
      rw [openGraph_adj_iff R.pData]
      exact ⟨m, hmA, Or.inl rfl⟩
    exact propext (R.botComp_of_adj C hadj)
  -- statuses of the bottom and top rows
  have hbotX : ∀ c : Cell, ∀ hc : c ∈ R.pcells, c.2 = R.y0 → X c := fun c hc hy =>
    ⟨hc, ⟨c, hc⟩, hy, SimpleGraph.Reachable.refl _⟩
  have htopX : ∀ c : Cell, c ∈ R.pcells → c.2 = R.y0 + R.h → ¬ X c := by
    rintro c hc hy ⟨_, b, hb, hconn⟩
    exact hno ⟨b, ⟨c, hc⟩, hb, hy, hconn⟩
  have hwbot : R.wcell R.y0 ∈ R.pcells := by
    rw [mem_pcells, mem_cells]
    have := R.wcell_primal R.y0
    have h2 := R.wcell_row R.y0
    have h3 := R.wcell_col R.y0
    refine ⟨⟨?_, ?_, ?_, ?_⟩, this⟩ <;> omega
  have hwtop : R.wcell (R.y0 + R.h) ∈ R.pcells := by
    rw [mem_pcells, mem_cells]
    have := R.wcell_primal (R.y0 + R.h)
    have h2 := R.wcell_row (R.y0 + R.h)
    have h3 := R.wcell_col (R.y0 + R.h)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, this⟩ <;> omega
  have hXbot : X (R.wcell R.y0) := hbotX _ hwbot (R.wcell_row _)
  have hXtop : ¬ X (R.wcell (R.y0 + R.h)) := htopX _ hwtop (R.wcell_row _)
  -- handshake
  have hdisj : Disjoint R.leftFaces R.rightFaces := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [leftFaces, rightFaces, Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
    omega
  obtain ⟨b, hb, t, ht, hr⟩ := R.dual_reachable_of_odd hEsub R.leftFaces R.rightFaces hdisj
    (by
      intro z hz1 hz2
      simp only [leftFaces, rightFaces, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
      have hzc := mem_cells.1 (mem_dcells.1 z.2).1
      have hz := mem_dcells.1 z.2
      have hx1 : R.x0 < z.1.1 := by omega
      have hx2 : z.1.1 < R.x0 + R.w := by omega
      obtain ⟨hW, hE'⟩ := R.outer_pcells z hx1 hx2
      rw [cutSet_filter_corners]
      refine cut_deg_even R hh X z.1 hz.2 hx1 hx2 hzc.2.2.1 hzc.2.2.2 ?_ ?_
      · intro hy
        constructor <;> intro _
        · exact hbotX _ hE' (by simp [hy])
        · exact hbotX _ hW (by simp [hy])
      · intro hy
        constructor <;> intro h
        · exact absurd h (htopX _ hW (by simp [hy]))
        · exact absurd h (htopX _ hE' (by simp [hy])))
    (by
      rw [R.leftSum_eq E hEsub]
      exact R.cutSet_col_odd hw X hXbot hXtop)
  have hb' : b.1.1 = R.x0 := by
    simp only [leftFaces, Finset.mem_filter, Finset.mem_univ, true_and] at hb; exact hb
  have ht' : t.1.1 = R.x0 + R.w := by
    simp only [rightFaces, Finset.mem_filter, Finset.mem_univ, true_and] at ht; exact ht
  exact ⟨b, t, hb', ht', R.dualOf_actualConnected hEc Finset.sdiff_subset hr⟩

end Rect

end PottsDiscontinuity.TorusCrossing
