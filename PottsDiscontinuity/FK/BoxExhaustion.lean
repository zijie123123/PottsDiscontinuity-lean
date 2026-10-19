/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.Lattice
public import Mathlib.Tactic

/-!
# Cofinality of increasing lattice boxes

Nested exhaustive sequences of finite lattice boxes eventually contain each
fixed finite lattice box. The canonical origin-centered boxes are nested and
exhaust the square lattice.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

/-- Nesting propagates box containment to every later index. -/
theorem latticeBox_subset_of_nested {c : ℕ → LatticeVertex} {r : ℕ → ℕ}
    (hnest : ∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1)))
    {m n : ℕ} (hmn : m ≤ n) :
    latticeBox (c m) (r m) ⊆ latticeBox (c n) (r n) := by
  induction hmn with
  | refl => exact subset_rfl
  | @step n hmn ih => exact ih.trans (hnest n)

/-- A nested exhaustive sequence of boxes eventually contains any fixed box. -/
theorem latticeBox_subset_eventually_of_nested_exhaustive
    {c : ℕ → LatticeVertex} {r : ℕ → ℕ}
    (hnest : ∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1)))
    (hexhaust : ∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n))
    (a : LatticeVertex) (R : ℕ) :
    ∃ N, ∀ n ≥ N, latticeBox a R ⊆ latticeBox (c n) (r n) := by
  classical
  let i : LatticeVertex → ℕ := fun v => Classical.choose (hexhaust v)
  let N := (latticeBox a R).sup i
  refine ⟨N, fun n hn v hv => ?_⟩
  have hi : i v ≤ N := Finset.le_sup hv
  have hiv : v ∈ latticeBox (c (i v)) (r (i v)) := Classical.choose_spec (hexhaust v)
  exact (latticeBox_subset_of_nested hnest (hi.trans hn)) hiv

/-- The canonical origin-centered boxes are nested. -/
theorem origin_latticeBox_nested (n : ℕ) :
    latticeBox (0, 0) n ⊆ latticeBox (0, 0) (n + 1) :=
  latticeBox_mono (0, 0) (Nat.le_succ n)

/-- Every lattice vertex lies in some canonical origin-centered box. -/
theorem origin_latticeBox_exhaustive (v : LatticeVertex) :
    ∃ n, v ∈ latticeBox (0, 0) n := by
  refine ⟨max v.1.natAbs v.2.natAbs, ?_⟩
  rw [mem_latticeBox]
  constructor <;> constructor <;> simp only [zero_sub, zero_add] <;> omega

end PottsDiscontinuity.FK
