module

public import PottsDiscontinuity.FK.Wiring
public import PottsDiscontinuity.TorusCrossing.Cochain
public import PottsDiscontinuity.TorusCrossing.Planar

/-!
# Exclusion: a primal connection and a crossing dual connection cannot coexist

If two primal cells are connected (with the bottom and top rows wired) in the configuration `A`,
then the dual endpoints of any closed edge `m` joining them cannot be connected (with left and
right columns wired) in the dual configuration `inner \ insert m A`.  The proof turns the primal
connection into a closed cochain (a primal cycle closed up by the collar zigzags that realise the
wiring) and evaluates its left-ray primitive.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity

namespace Rect

variable (R : Rect)

/-- The medial vertices of the zigzags just outside the bottom and top rows. -/
def collarAll : Finset Cell :=
  collar R.y0 R.x0 (R.x0 + R.w) ∪ collar (R.y0 + R.h + 1) R.x0 (R.x0 + R.w)

/-- The relation "joined by a chain of open edges and collar zigzags", as a `ZMod 2` cochain. -/
def cochainRel (A : Finset Cell) (x y : R.pcells) : Prop :=
  ∃ f : Cell → ZMod 2, (∀ m, f m ≠ 0 → m ∈ A ∨ m ∈ R.collarAll) ∧
    ∀ c, IsPrimal c → cdeg f c = (if c = x.1 then 1 else 0) + (if c = y.1 then 1 else 0)

theorem cochainRel_refl (A : Finset Cell) (x : R.pcells) : R.cochainRel A x x := by
  refine ⟨fun _ => 0, fun m hm => absurd rfl hm, fun c _ => ?_⟩
  rw [cdeg_zero]
  split_ifs <;> decide

theorem cochainRel_symm (A : Finset Cell) {x y : R.pcells} (h : R.cochainRel A x y) :
    R.cochainRel A y x := by
  obtain ⟨f, hf, hdeg⟩ := h
  exact ⟨f, hf, fun c hc => by rw [hdeg c hc, add_comm]⟩

theorem cochainRel_trans (A : Finset Cell) {x y z : R.pcells} (h : R.cochainRel A x y)
    (h' : R.cochainRel A y z) : R.cochainRel A x z := by
  obtain ⟨f, hf, hdeg⟩ := h
  obtain ⟨g, hg, hdeg'⟩ := h'
  refine ⟨fun m => f m + g m, ?_, ?_⟩
  · intro m hm
    change f m + g m ≠ 0 at hm
    by_cases h1 : f m = 0
    · rw [h1, zero_add] at hm; exact hg m hm
    · exact hf m h1
  · intro c hc
    rw [cdeg_add, hdeg c hc, hdeg' c hc]
    generalize (if c = x.1 then (1 : ZMod 2) else 0) = a
    generalize (if c = y.1 then (1 : ZMod 2) else 0) = b
    generalize (if c = z.1 then (1 : ZMod 2) else 0) = d
    revert a b d; decide

/-- The setoid of chain-connected primal cells. -/
def cochainSetoid (A : Finset Cell) : Setoid R.pcells where
  r := R.cochainRel A
  iseqv := ⟨R.cochainRel_refl A, R.cochainRel_symm A, R.cochainRel_trans A⟩

theorem collar_bottom_subset (lo hi : ℤ) (h1 : R.x0 ≤ lo) (h2 : hi ≤ R.x0 + R.w) :
    collar R.y0 lo hi ⊆ R.collarAll := by
  intro m hm
  rw [mem_collar] at hm
  unfold collarAll
  rw [Finset.mem_union, mem_collar, mem_collar]
  left; omega

theorem collar_top_subset (lo hi : ℤ) (h1 : R.x0 ≤ lo) (h2 : hi ≤ R.x0 + R.w) :
    collar (R.y0 + R.h + 1) lo hi ⊆ R.collarAll := by
  intro m hm
  rw [mem_collar] at hm
  unfold collarAll
  rw [Finset.mem_union, mem_collar, mem_collar]
  right; omega

/-- A wiring relation between two cells of the same boundary row is a chain relation. -/
theorem cochainRel_of_row (A : Finset Cell) (a b : R.pcells) (r r' : ℤ)
    (hr : r' = R.y0 ∧ r = R.y0 ∨ r' = R.y0 + R.h ∧ r = R.y0 + R.h + 1)
    (ha : a.1.2 = r') (hb : b.1.2 = r') : R.cochainRel A a b := by
  have hac := mem_cells.1 (mem_pcells.1 a.2).1
  have hbc := mem_cells.1 (mem_pcells.1 b.2).1
  have hap := (mem_pcells.1 a.2).2
  have hbp := (mem_pcells.1 b.2).2
  have hrr : r' = r ∨ r' = r - 1 := by omega
  rcases le_total a.1.1 b.1.1 with hab | hab
  · refine ⟨ind (collar r a.1.1 b.1.1), ?_, ?_⟩
    · intro m hm
      right
      have : m ∈ collar r a.1.1 b.1.1 := by
        by_contra hn; exact hm (ind_apply_of_not_mem hn)
      rcases hr with hr | hr
      · rw [hr.2] at this
        exact R.collar_bottom_subset _ _ hac.1 hbc.2.1 this
      · rw [hr.2] at this
        exact R.collar_top_subset _ _ hac.1 hbc.2.1 this
    · intro c hc
      have hlo : IsPrimal (a.1.1, r') := by
        have := hap; unfold IsPrimal at *; rw [ha] at this; exact this
      have hhi : IsPrimal (b.1.1, r') := by
        have := hbp; unfold IsPrimal at *; rw [hb] at this; exact this
      rw [cdeg_collar r a.1.1 b.1.1 hab r' hrr hlo hhi c hc]
      have ea : (a.1.1, r') = a.1 := Prod.ext rfl ha.symm
      have eb : (b.1.1, r') = b.1 := Prod.ext rfl hb.symm
      rw [ea, eb]
  · refine ⟨ind (collar r b.1.1 a.1.1), ?_, ?_⟩
    · intro m hm
      right
      have : m ∈ collar r b.1.1 a.1.1 := by
        by_contra hn; exact hm (ind_apply_of_not_mem hn)
      rcases hr with hr | hr
      · rw [hr.2] at this
        exact R.collar_bottom_subset _ _ hbc.1 hac.2.1 this
      · rw [hr.2] at this
        exact R.collar_top_subset _ _ hbc.1 hac.2.1 this
    · intro c hc
      have hlo : IsPrimal (b.1.1, r') := by
        have := hbp; unfold IsPrimal at *; rw [hb] at this; exact this
      have hhi : IsPrimal (a.1.1, r') := by
        have := hap; unfold IsPrimal at *; rw [ha] at this; exact this
      rw [cdeg_collar r b.1.1 a.1.1 hab r' hrr hlo hhi c hc]
      have ea : (a.1.1, r') = a.1 := Prod.ext rfl ha.symm
      have eb : (b.1.1, r') = b.1 := Prod.ext rfl hb.symm
      rw [ea, eb, add_comm]

/-- Open connectivity with wired rows is a chain relation. -/
theorem sep_le_cochain (A : Finset Cell) (hA : A ⊆ R.inner) :
    FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A) ≤ R.cochainSetoid A := by
  apply FK.componentSetoid_le
  · intro u v huv
    have hle : (FK.openGraph R.pG (cfgOf R.pData A)).reachableSetoid ≤ R.cochainSetoid A := by
      apply FK.reachableSetoid_le_of_adj
      intro x y hxy
      have hxy' := (openGraph_adj_iff R.pData (cfgOf R.pData A) x y).1 hxy
      rw [openMedials_cfgOf R.pData A hA] at hxy'
      obtain ⟨m, hm, hmxy⟩ := hxy'
      refine ⟨ind {m}, ?_, ?_⟩
      · intro m' hm'
        left
        have : m' ∈ ({m} : Finset Cell) := by
          by_contra hn; exact hm' (ind_apply_of_not_mem hn)
        rw [Finset.mem_singleton] at this; rw [this]; exact hm
      · intro c hc
        rw [cdeg_ind_single m c hc]
        rcases hmxy with h | h
        · rw [h]
        · rw [h, add_comm]
    exact hle huv
  · intro a b hab
    rcases hab with h | h | h
    · subst h; exact R.cochainRel_refl A a
    · exact R.cochainRel_of_row A a b R.y0 R.y0 (Or.inl ⟨rfl, rfl⟩) h.1 h.2
    · exact R.cochainRel_of_row A a b (R.y0 + R.h + 1) (R.y0 + R.h)
        (Or.inr ⟨rfl, rfl⟩) h.1 h.2


theorem not_mem_collarAll_of_inner {m : Cell} (hm : m ∈ R.inner) : m ∉ R.collarAll := by
  intro h
  unfold collarAll at h
  rw [Finset.mem_union, mem_collar, mem_collar] at h
  rw [mem_inner] at hm
  omega

theorem mem_collarAll {m : Cell} (h : m ∈ R.collarAll) :
    R.x0 < m.1 ∧ m.1 ≤ R.x0 + R.w ∧ (m.2 = R.y0 ∨ m.2 = R.y0 + R.h + 1) := by
  unfold collarAll at h
  rw [Finset.mem_union, mem_collar, mem_collar] at h
  omega

/-- The dual wiring: left and right columns of odd cells. -/
def dualBC : FK.BoundaryCondition R.dcells :=
  FK.BoundaryCondition.wired {z | z.1.1 = R.x0 ∨ z.1.1 = R.x0 + R.w}

/-- **Exclusion.**  If two primal cells joined by a closed edge `m` are already connected
(with wired rows), the dual endpoints of `m` are not connected in the complementary dual
configuration (with wired side columns). -/
theorem exclusion (A : Finset Cell) (hA : A ⊆ R.inner) (m : Cell) (hm : m ∈ R.inner)
    (hmA : m ∉ A) (u v : R.pcells) (hu : u.1 = (primalEnds m).1) (hv : v.1 = (primalEnds m).2)
    (u' v' : R.dcells) (hu' : u'.1 = (dualEnds m).1) (hv' : v'.1 = (dualEnds m).2)
    (hrel : (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r u v) :
    ¬ (FK.componentSetoid R.dG R.dualBC (cfgOf R.dData (R.inner \ insert m A))).r u' v' := by
  intro hdual
  obtain ⟨f, hf, hdeg⟩ := R.sep_le_cochain A hA hrel
  set C₀ : Cell → ZMod 2 := fun m' => f m' + ind {m} m' with hC₀
  have hclosed : ∀ c, IsPrimal c → cdeg C₀ c = 0 := by
    intro c hc
    rw [hC₀, cdeg_add, hdeg c hc, cdeg_ind_single m c hc, hu, hv]
    generalize (if c = (primalEnds m).1 then (1 : ZMod 2) else 0) = a
    generalize (if c = (primalEnds m).2 then (1 : ZMod 2) else 0) = b
    revert a b; decide
  have hsupp : ∀ m', C₀ m' ≠ 0 → R.x0 < m'.1 ∧ m'.1 ≤ R.x0 + R.w ∧ R.y0 ≤ m'.2 := by
    intro m' hm'
    change f m' + ind {m} m' ≠ 0 at hm'
    by_cases h1 : f m' = 0
    · rw [h1, zero_add] at hm'
      have : m' ∈ ({m} : Finset Cell) := by
        by_contra hn; exact hm' (ind_apply_of_not_mem hn)
      rw [Finset.mem_singleton] at this; subst this
      rw [mem_inner] at hm; omega
    · rcases hf m' h1 with h | h
      · have := hA h; rw [mem_inner] at this; omega
      · have := R.mem_collarAll h; omega
  have hx0 : ∀ m' : Cell, m'.1 ≤ R.x0 → C₀ m' = 0 := by
    intro m' h; by_contra hne; have := hsupp m' hne; omega
  have hxw : ∀ m' : Cell, R.x0 + (R.w : ℤ) < m'.1 → C₀ m' = 0 := by
    intro m' h; by_contra hne; have := hsupp m' hne; omega
  have hy0 : ∀ m' : Cell, m'.2 ≤ R.y0 - 1 → C₀ m' = 0 := by
    intro m' h; by_contra hne; have := hsupp m' hne; omega
  have hclosed' : ∀ c : Cell, IsPrimal c → R.x0 ≤ c.1 → c.1 ≤ R.x0 + R.w → cdeg C₀ c = 0 :=
    fun c hc _ _ => hclosed c hc
  set g : Cell → ZMod 2 := leftPotential R.x0 (R.y0 - 1) C₀ with hg
  have hprim : ∀ m' : Cell, R.x0 < m'.1 → m'.1 ≤ R.x0 + R.w →
      g (dualEnds m').1 + g (dualEnds m').2 = C₀ m' := fun m' h1 h2 =>
    leftPotential_primitive R.x0 (R.y0 - 1) R.w C₀ hx0 hy0
      (fun c hc _ _ => hclosed c hc) m' h1 h2
  have hzero : ∀ z : Cell, z.1 = R.x0 ∨ z.1 = R.x0 + R.w → g z = 0 := by
    intro z hz
    exact leftPotential_zero_of_closed R.x0 (R.y0 - 1) R.w C₀ hx0 hxw hy0 hclosed' (by positivity)
      z (by omega)
  -- the dual component relation is contained in the kernel of `g`
  have hker : FK.componentSetoid R.dG R.dualBC (cfgOf R.dData (R.inner \ insert m A)) ≤
      Setoid.ker (fun z : R.dcells => g z.1) := by
    apply FK.componentSetoid_le
    · intro x y hxy
      have hle : (FK.openGraph R.dG (cfgOf R.dData (R.inner \ insert m A))).reachableSetoid ≤
          Setoid.ker (fun z : R.dcells => g z.1) := by
        apply FK.reachableSetoid_le_of_adj
        intro x y hxy
        have hxy' := (openGraph_adj_iff R.dData _ x y).1 hxy
        rw [openMedials_cfgOf R.dData _ Finset.sdiff_subset] at hxy'
        obtain ⟨m', hm', hmxy⟩ := hxy'
        rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hm'
        obtain ⟨hmi, hm1, hm2⟩ := hm'
        have hmi' := mem_inner.1 hmi
        have h0 : C₀ m' = 0 := by
          change f m' + ind {m} m' = 0
          have e1 : f m' = 0 := by
            by_contra hne
            rcases hf m' hne with h | h
            · exact hm2 h
            · exact R.not_mem_collarAll_of_inner hmi h
          have e2 : ind {m} m' = 0 := ind_apply_of_not_mem (by simpa using hm1)
          rw [e1, e2]; simp
        have hs := hprim m' (by omega) (by omega)
        rw [h0] at hs
        show g x.1 = g y.1
        rcases hmxy with h | h
        · rw [h] at hs
          have := zmod2_two (g x.1)
          have h3 : g x.1 + g y.1 = 0 := hs
          calc g x.1 = g x.1 + (g y.1 + g y.1) := by rw [zmod2_two, add_zero]
            _ = (g x.1 + g y.1) + g y.1 := by ring
            _ = g y.1 := by rw [h3, zero_add]
        · rw [h] at hs
          have h3 : g y.1 + g x.1 = 0 := hs
          calc g x.1 = g x.1 + (g y.1 + g y.1) := by rw [zmod2_two, add_zero]
            _ = (g y.1 + g x.1) + g y.1 := by ring
            _ = g y.1 := by rw [h3, zero_add]
      exact hle hxy
    · intro a b hab
      rcases hab with h | ⟨ha, hb⟩
      · subst h; rfl
      · show g a.1 = g b.1
        rw [hzero a.1 ha, hzero b.1 hb]
  have hker' := hker hdual
  have hgeq : g u'.1 = g v'.1 := hker'
  have hs := hprim m (by rw [mem_inner] at hm; omega) (by rw [mem_inner] at hm; omega)
  have hfm : f m = 0 := by
    by_contra hne
    rcases hf m hne with h | h
    · exact hmA h
    · exact R.not_mem_collarAll_of_inner hm h
  have hCm : C₀ m = 1 := by
    change f m + ind {m} m = 1
    rw [hfm, ind_apply_of_mem (Finset.mem_singleton_self m)]; simp
  rw [hCm, ← hu', ← hv', hgeq, zmod2_two] at hs
  exact absurd hs (by decide)

end Rect

end PottsDiscontinuity.TorusCrossing
