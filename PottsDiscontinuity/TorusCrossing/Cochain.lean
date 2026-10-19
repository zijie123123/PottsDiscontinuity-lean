module

public import PottsDiscontinuity.TorusCrossing.Exact

/-!
# Indicator cochains: edges and collar paths

`ind A` is the `ZMod 2`-valued indicator of a finite set of medial vertices.  The degree of the
indicator of the single medial vertex `m` at a primal cell is `1` exactly at the two ends of the
primal edge at `m`.  A *collar interval* is the indicator of the medial vertices
`(a, r)` with `lo < a ≤ hi` on one row `r`; it has odd degree exactly at the two primal cells
`(lo, r')`, `(hi, r')` with `r' ∈ {r, r-1}` and even degree elsewhere (it is the zigzag path
running just outside a wired row).
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

/-- Indicator cochain of a finite set of medial vertices. -/
def ind (A : Finset Cell) : Cell → ZMod 2 := fun m => if m ∈ A then 1 else 0

theorem ind_apply_of_mem {A : Finset Cell} {m : Cell} (h : m ∈ A) : ind A m = 1 := by
  simp [ind, h]

theorem ind_apply_of_not_mem {A : Finset Cell} {m : Cell} (h : m ∉ A) : ind A m = 0 := by
  simp [ind, h]

theorem cdeg_add (f g : Cell → ZMod 2) (c : Cell) :
    cdeg (fun m => f m + g m) c = cdeg f c + cdeg g c := by
  unfold cdeg; ring

theorem cdeg_zero (c : Cell) : cdeg (fun _ => (0 : ZMod 2)) c = 0 := by
  unfold cdeg; simp

theorem zmod2_two (z : ZMod 2) : z + z = 0 := by fin_cases z <;> decide

/-- The degree of the indicator of a single medial vertex at a primal cell. -/
theorem cdeg_ind_single (m c : Cell) (hc : IsPrimal c) :
    cdeg (ind {m}) c =
      (if c = (primalEnds m).1 then 1 else 0) + (if c = (primalEnds m).2 then 1 else 0) := by
  have hne := primalEnds_ne m
  have h := mem_primalEnds_iff c m hc
  unfold cdeg ind
  simp only [Finset.mem_singleton]
  unfold primalEnds IsPrimal at *
  unfold corners at h
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at h
  split_ifs at h hne ⊢ <;> simp only [Prod.ext_iff] at * <;> first | omega | decide

/-- Row-interval collar cochain. -/
def collar (r lo hi : ℤ) : Finset Cell := Finset.Ioc lo hi ×ˢ {r}

theorem mem_collar {r lo hi : ℤ} {m : Cell} : m ∈ collar r lo hi ↔ lo < m.1 ∧ m.1 ≤ hi ∧ m.2 = r := by
  unfold collar; simp only [Finset.mem_product, Finset.mem_Ioc, Finset.mem_singleton]; tauto

/-- Degree of a collar interval at a primal cell whose row is `r` or `r - 1`. -/
theorem cdeg_collar (r lo hi : ℤ) (hlohi : lo ≤ hi) (r' : ℤ) (hr' : r' = r ∨ r' = r - 1)
    (hlo : IsPrimal (lo, r')) (hhi : IsPrimal (hi, r')) (c : Cell) (hc : IsPrimal c) :
    cdeg (ind (collar r lo hi)) c =
      (if c = (lo, r') then 1 else 0) + (if c = (hi, r') then 1 else 0) := by
  unfold cdeg ind
  simp only [mem_collar]
  unfold IsPrimal at *
  by_cases hlh : lo = hi
  · subst hlh
    split_ifs <;> simp only [Prod.ext_iff] at * <;> first | omega | decide
  · split_ifs <;> simp only [Prod.ext_iff] at * <;> first | omega | decide

end PottsDiscontinuity.TorusCrossing
