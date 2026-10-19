module

public import PottsDiscontinuity.SixVertex.Defs

/-! # Half filling: largest eigenvalue and simplicity -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

/-- The even-position staggered state on a row of length `2n`. -/
def evenState (n : ℕ) : State (2 * n) n :=
  ⟨univ.image (fun i : Fin n => (⟨2 * i.val, by omega⟩ : Fin (2 * n))), by
    rw [card_image_of_injective, card_univ, Fintype.card_fin]
    intro i j he
    apply Fin.ext
    have := congrArg Fin.val he
    dsimp at this
    omega⟩

theorem mem_evenState {n : ℕ} (i : Fin (2 * n)) : i ∈ (evenState n).1 ↔ i.val % 2 = 0 := by
  change i ∈ univ.image _ ↔ _
  constructor
  · intro hi
    obtain ⟨j, _, hj⟩ := mem_image.mp hi
    have hv := congrArg Fin.val hj
    dsimp at hv
    omega
  · intro hi
    refine mem_image.mpr ⟨⟨i.val / 2, by omega⟩, mem_univ _, ?_⟩
    apply Fin.ext
    dsimp
    omega

end PottsDiscontinuity.SixVertex
