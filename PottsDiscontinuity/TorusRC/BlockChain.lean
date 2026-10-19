module

public import PottsDiscontinuity.TorusRC.ReflectedPairs

/-! # Iterating the reflected double-block connection bound -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- Reflect the base double-height block into block j of the lifted chain. -/
def rectangleBlockEvent (hNp : 0 < N) (hMp : 0 < M) (n : ℕ)
    (i : Fin (3 * n + 1)) (j : ℕ) : Set (RCConfig N M) :=
  reflectRCConfig hMp (2 * (n : ℤ) * ((j : ℤ) + 1)) ⁻¹'
    rectangleDoubleConnection hNp hMp n i

theorem rectangleDoubleConnection_mono (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (i : Fin (3 * n + 1)) {A B : RCConfig N M} (hAB : A ≤ B)
    (hA : A ∈ rectangleDoubleConnection hNp hMp n i) :
    B ∈ rectangleDoubleConnection hNp hMp n i := by
  obtain ⟨u,v,hu,hv,w,hw⟩ := hA
  let F : liftedStripGraph hNp hMp A 0 (3 * (n : ℤ)) →g
      liftedStripGraph hNp hMp B 0 (3 * (n : ℤ)) :=
    ⟨id,fun h => liftedStripGraph_mono hNp hMp 0 (3 * (n : ℤ)) hAB h⟩
  refine ⟨u,v,hu,hv,w.map F,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨z',hz',heq⟩ := List.mem_map.mp hz
  change z' = z at heq
  subst z
  exact hw z' hz'

/-- FKG k times, using the exact reflection symmetry at every block. -/
theorem rectangleBlocks_probability_ge_power (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ))
    (n : ℕ) (i : Fin (3 * n + 1)) (k : ℕ) :
    torusRCProbability hN hM q (rectangleDoubleConnection hNp hMp n i) ^ k ≤
      torusRCProbability hN hM q {A | ∀ j < k, A ∈ rectangleBlockEvent hNp hMp n i j} := by
  classical
  let E : Fin k → Set (RCConfig N M) := fun j => rectangleBlockEvent hNp hMp n i j.val
  have hE : ∀ j ⦃A B⦄, A ≤ B → A ∈ E j → B ∈ E j := by
    intro j A B hAB hA
    exact rectangleDoubleConnection_mono hNp hMp n i (fun e => hAB _) hA
  have h := torusRCProbability_finset_inter_ge_prod hN hM q Finset.univ E hE
  have heq (j : Fin k) : torusRCProbability hN hM q (E j) =
      torusRCProbability hN hM q (rectangleDoubleConnection hNp hMp n i) :=
    (torusRCProbability_reflect hN hM hNp hMp (2 * (n : ℤ) * ((j.val : ℤ) + 1))
      ⟨(n : ℤ) * (j.val + 1),by ring⟩ q _).symm
  simp_rw [heq] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have hset : {A | ∀ j ∈ (Finset.univ : Finset (Fin k)), A ∈ E j} =
      {A | ∀ j < k, A ∈ rectangleBlockEvent hNp hMp n i j} := by
    ext A
    simp only [Finset.mem_univ, true_implies]
    constructor
    · intro h j hj
      exact h ⟨j,hj⟩
    · intro h j
      exact h j.val j.isLt
  rwa [hset] at h

end PottsDiscontinuity.TorusRC
