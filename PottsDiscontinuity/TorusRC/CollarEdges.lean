module

public import PottsDiscontinuity.FK.EdgeRestriction
public import PottsDiscontinuity.TorusRC.BarrierSeam
public import PottsDiscontinuity.TorusRC.RightHalf
public import PottsDiscontinuity.TorusRC.SeamCollar

/-! # A bounded set of retained edges sufficient for both seam collars -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- At most 2L integer steps, covering the bottom and top collars. -/
def collarTimes (M L : ℕ) : Finset ℕ :=
  Finset.range L ∪ (Finset.range L).image (fun k => M - 1 - k)

theorem collarTimes_card_le (M L : ℕ) : (collarTimes M L).card ≤ 2 * L := by
  calc
    _ ≤ (Finset.range L).card + ((Finset.range L).image (fun k => M - 1 - k)).card :=
      Finset.card_union_le _ _
    _ ≤ L + L := Nat.add_le_add (by simp) ((Finset.card_image_le).trans_eq (by simp))
    _ = 2 * L := by omega

theorem mem_collarTimes (M L k : ℕ) (hk : k < M)
    (hcollar : k < L ∨ M - L ≤ k) : k ∈ collarTimes M L := by
  rcases hcollar with h | h
  · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨M - 1 - k, Finset.mem_range.mpr (by omega), by omega⟩

noncomputable section

/-- The seam itself is excluded: B already forces its right-hand edges open. -/
def columnCollarEdges (hNp : 0 < N) (hMp : 0 < M) (x : ℤ) (L : ℕ) :
    Finset (Fin N × Fin M) :=
  ((collarTimes M L).image (fun k : ℕ =>
    (periodicCoordinate hNp (x + 1), periodicCoordinate hMp ((k : ℤ) + 1)))).filter
      (fun e => e.2.val ≠ 0)

theorem columnCollarEdges_card_le (hNp : 0 < N) (hMp : 0 < M) (x : ℤ) (L : ℕ) :
    (columnCollarEdges hNp hMp x L).card ≤ 2 * L :=
  (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (collarTimes_card_le M L))

theorem periodicCoordinate_rightHalf (hNp : 0 < N) (x : ℤ)
    (hxleft : (N / 2 : ℤ) ≤ x) (hxright : x + 1 ≤ (N : ℤ)) :
    (periodicCoordinate hNp (x + 1)).val = 0 ∨
      N / 2 < (periodicCoordinate hNp (x + 1)).val := by
  have hx0 : 0 < x + 1 := by omega
  by_cases heq : x + 1 = (N : ℤ)
  · left
    have hv := periodicCoordinate_val hNp (x + 1)
    rw [heq, Int.emod_self] at hv
    rw [heq]
    exact_mod_cast hv
  · right
    have hv := periodicCoordinate_val hNp (x + 1)
    rw [Int.emod_eq_of_lt hx0.le (by omega)] at hv
    omega

theorem columnCollarEdges_interior (hNp : 0 < N) (hMp : 0 < M) (x : ℤ) (L : ℕ)
    (hxleft : (N / 2 : ℤ) ≤ x) (hxright : x + 1 ≤ (N : ℤ))
    (e : Fin N × Fin M) (he : e ∈ columnCollarEdges hNp hMp x L) :
    rightHalfInteriorSite e := by
  obtain ⟨he, hrow⟩ := Finset.mem_filter.mp he
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp he
  exact ⟨periodicCoordinate_rightHalf hNp x hxleft hxright, hrow⟩

/-- B supplies the seam edge; the retained collar set supplies every other
edge needed by the two finite zigzag collars. -/
theorem columnCollarOpen_of_barrier_and_edges (hNp : 0 < N) (hMp : 0 < M)
    (x : ℤ) (L n : ℕ) (hxleft : (N / 2 : ℤ) ≤ x)
    (hxright : x + 1 ≤ (N : ℤ)) (hn : 3 * n ≤ N / 2)
    (A : RCConfig N M) (hB : A ∈ torusRCBarrier hNp hMp n)
    (hopen : ∀ e ∈ columnCollarEdges hNp hMp x L, A e = true) :
    columnCollarOpen hNp hMp x L A := by
  intro k hk hcollar
  have hi := periodicCoordinate_rightHalf hNp x hxleft hxright
  by_cases hrow : (periodicCoordinate hMp ((k : ℤ) + 1)).val = 0
  · have hy : periodicCoordinate hMp ((k : ℤ) + 1) = (⟨0,hMp⟩ : Fin M) := Fin.ext hrow
    rw [hy]
    apply barrier_seam_open_outside_left_strip hNp hMp A n (by omega) hB
    rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (by omega)
  · apply hopen
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨k, mem_collarTimes M L k hk hcollar, rfl⟩, hrow⟩

/-- A finite indexed interior edge set, viewed in the retained simple graph. -/
def rightHalfRetainedSet (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (s : Finset (Fin N × Fin M)) (hs : ∀ e ∈ s, rightHalfInteriorSite e) :
    FK.Configuration (FK.edgeRestriction (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) :=
  (FK.edgeRestrictionConfigurationEquiv (fullDiamondGraph hN hM)
    (rightHalfFrozenEdges hN hM hN4 hM4)).symm
    ⟨s.map (torusIndexedEdgeEquiv hN hM hN4 hM4).toEmbedding, by
      apply Finset.disjoint_left.mpr
      intro e he heF
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp he
      exact ((mem_rightHalfFrozenEdges hN hM hN4 hM4 v).mp heF) (hs v hv)⟩

theorem rightHalfRetainedSet_val (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (s : Finset (Fin N × Fin M)) (hs : ∀ e ∈ s, rightHalfInteriorSite e) :
    (FK.edgeRestrictionConfigurationEquiv (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)
      (rightHalfRetainedSet hN hM hN4 hM4 s hs)).val =
      s.map (torusIndexedEdgeEquiv hN hM hN4 hM4).toEmbedding := by
  exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

theorem rightHalfRetainedSet_card (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (s : Finset (Fin N × Fin M)) (hs : ∀ e ∈ s, rightHalfInteriorSite e) :
    (rightHalfRetainedSet hN hM hN4 hM4 s hs).card = s.card := by
  rw [← FK.card_edgeRestrictionConfigurationEquiv (fullDiamondGraph hN hM)
    (rightHalfFrozenEdges hN hM hN4 hM4), rightHalfRetainedSet_val, Finset.card_map]

theorem rightHalfRetainedSet_open (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (s : Finset (Fin N × Fin M)) (hs : ∀ e ∈ s, rightHalfInteriorSite e)
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (A : FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (hopen : (FK.edgeRestrictionConfigurationEquiv (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)
      (rightHalfRetainedSet hN hM hN4 hM4 s hs)).val ⊆ A.val) :
    ∀ e ∈ s, rightHalfRestore hN hM hN4 hM4 H A e = true := by
  classical
  rw [rightHalfRetainedSet_val] at hopen
  intro e he
  apply (rightHalfRestore_true_iff hN hM hN4 hM4 H A e).mpr
  exact Or.inl (hopen (Finset.mem_map.mpr ⟨e,he,rfl⟩))

end

end PottsDiscontinuity.TorusRC
