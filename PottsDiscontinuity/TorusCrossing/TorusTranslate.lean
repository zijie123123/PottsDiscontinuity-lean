module

public import PottsDiscontinuity.TorusCrossing.TorusEvents
public import PottsDiscontinuity.TorusRC.ReflectionGraph

/-!
# Translation invariance of the indexed torus law

For `a + b` even, the translation of the indexed configuration by `(a, b)` preserves the cluster
count, hence the law.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open PottsDiscontinuity.TorusRC Torus CorrLength PottsDiscontinuity.SixVertex
open PottsDiscontinuity.TorusTopology
open scoped Classical

variable {N M : ℕ}

theorem periodicCoordinate_congr (hp : 0 < N) {z z' : ℤ} (h : z % (N : ℤ) = z' % (N : ℤ)) :
    periodicCoordinate hp z = periodicCoordinate hp z' := by
  apply Fin.ext
  unfold periodicCoordinate
  simp only [h]

theorem periodicCoordinate_val_add (hp : 0 < N) (z a : ℤ) :
    periodicCoordinate hp (((periodicCoordinate hp z).val : ℤ) + a) = periodicCoordinate hp (z + a) := by
  apply periodicCoordinate_congr
  rw [periodicCoordinate_val, Int.emod_add_emod]

/-- Cyclic translation of a coordinate. -/
def periodicShift (hp : 0 < N) (a : ℤ) : Fin N ≃ Fin N where
  toFun j := periodicCoordinate hp ((j.val : ℤ) + a)
  invFun j := periodicCoordinate hp ((j.val : ℤ) - a)
  left_inv j := by
    change periodicCoordinate hp (((periodicCoordinate hp ((j.val : ℤ) + a)).val : ℤ) - a) = j
    rw [sub_eq_add_neg, periodicCoordinate_val_add, add_assoc, add_neg_cancel, add_zero,
      periodicCoordinate_nat hp]
  right_inv j := by
    change periodicCoordinate hp (((periodicCoordinate hp ((j.val : ℤ) - a)).val : ℤ) + a) = j
    rw [periodicCoordinate_val_add, sub_add_cancel, periodicCoordinate_nat hp]

theorem periodicShift_periodicCoordinate (hp : 0 < N) (a z : ℤ) :
    periodicShift hp a (periodicCoordinate hp z) = periodicCoordinate hp (z + a) :=
  periodicCoordinate_val_add hp z a

/-- Translation of the torus indices. -/
def shiftIdx (hNp : 0 < N) (hMp : 0 < M) (a b : ℤ) : (Fin N × Fin M) ≃ (Fin N × Fin M) :=
  Equiv.prodCongr (periodicShift hNp a) (periodicShift hMp b)

/-- Translation of an indexed configuration: `(translRC a b A) v = A (v + (a,b))`. -/
def translRC (hNp : 0 < N) (hMp : 0 < M) (a b : ℤ) (A : RCConfig N M) : RCConfig N M :=
  fun v => A (shiftIdx hNp hMp a b v)

/-- Translation of the lifted lattice by `(a, b)`, `a + b` even. -/
def shiftRV (a b : ℤ) (hab : Even (a + b)) (z : RotatedVertex) : RotatedVertex :=
  ⟨(z.val.1 + a, z.val.2 + b), by
    obtain ⟨k, hk⟩ := z.property
    obtain ⟨l, hl⟩ := hab
    exact ⟨k + l, by dsimp only at *; omega⟩⟩

theorem shiftRV_adj (a b : ℤ) (hab : Even (a + b)) {u v : RotatedVertex} :
    rotatedLattice.Adj (shiftRV a b hab u) (shiftRV a b hab v) ↔ rotatedLattice.Adj u v := by
  change (|(u.val.1 + a) - (v.val.1 + a)| = 1 ∧ |(u.val.2 + b) - (v.val.2 + b)| = 1) ↔
    (|u.val.1 - v.val.1| = 1 ∧ |u.val.2 - v.val.2| = 1)
  have h1 : (u.val.1 + a) - (v.val.1 + a) = u.val.1 - v.val.1 := by ring
  have h2 : (u.val.2 + b) - (v.val.2 + b) = u.val.2 - v.val.2 := by ring
  rw [h1, h2]

theorem liftedEdgeIndex_shift (hNp : 0 < N) (hMp : 0 < M) (a b : ℤ) (hab : Even (a + b))
    (u v : RotatedVertex) :
    liftedEdgeIndex hNp hMp (shiftRV a b hab u) (shiftRV a b hab v) =
      shiftIdx hNp hMp a b (liftedEdgeIndex hNp hMp u v) := by
  unfold liftedEdgeIndex shiftIdx
  apply Prod.ext
  · change periodicCoordinate hNp (max (u.val.1 + a) (v.val.1 + a)) =
      periodicShift hNp a (periodicCoordinate hNp (max u.val.1 v.val.1))
    rw [periodicShift_periodicCoordinate, max_add_add_right]
  · change periodicCoordinate hMp (max (u.val.2 + b) (v.val.2 + b)) =
      periodicShift hMp b (periodicCoordinate hMp (max u.val.2 v.val.2))
    rw [periodicShift_periodicCoordinate, max_add_add_right]

section Faces

variable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (a b : ℤ) (hab : Even (a + b))

/-- Translation of a primal torus vertex. -/
def translatePrimalFace (v : FaceVertex N M true) : FaceVertex N M true :=
  liftedFaceVertex hN hM hNp hMp (shiftRV a b hab (canonicalPrimalLift v))

theorem translatePrimalFace_projects (u : RotatedVertex) :
    translatePrimalFace hN hM hNp hMp a b hab (liftedFaceVertex hN hM hNp hMp u) =
      liftedFaceVertex hN hM hNp hMp (shiftRV a b hab u) := by
  apply Subtype.ext
  apply Prod.ext
  · change periodicCoordinate hNp (((periodicCoordinate hNp u.val.1).val : ℤ) + a) =
      periodicCoordinate hNp (u.val.1 + a)
    exact periodicCoordinate_val_add hNp _ _
  · change periodicCoordinate hMp (((periodicCoordinate hMp u.val.2).val : ℤ) + b) =
      periodicCoordinate hMp (u.val.2 + b)
    exact periodicCoordinate_val_add hMp _ _

theorem lifted_canonical (v : FaceVertex N M true) :
    liftedFaceVertex hN hM hNp hMp (canonicalPrimalLift v) = v := by
  apply Subtype.ext
  apply Prod.ext
  · exact periodicCoordinate_nat hNp _
  · exact periodicCoordinate_nat hMp _

theorem shiftRV_shiftRV (hab' : Even (-a + -b)) (u : RotatedVertex) :
    shiftRV (-a) (-b) hab' (shiftRV a b hab u) = u := by
  apply Subtype.ext
  apply Prod.ext <;> simp [shiftRV]

theorem shiftRV_shiftRV' (hab' : Even (-a + -b)) (u : RotatedVertex) :
    shiftRV a b hab (shiftRV (-a) (-b) hab' u) = u := by
  apply Subtype.ext
  apply Prod.ext <;> simp [shiftRV]

theorem even_neg_add (hab : Even (a + b)) : Even (-a + -b) := by
  have : -a + -b = -(a + b) := by ring
  rw [this]; exact hab.neg

/-- Translation of the primal vertices as an equivalence. -/
def translatePrimalFaceEquiv : FaceVertex N M true ≃ FaceVertex N M true where
  toFun := translatePrimalFace hN hM hNp hMp a b hab
  invFun := translatePrimalFace hN hM hNp hMp (-a) (-b) (even_neg_add a b hab)
  left_inv v := by
    change translatePrimalFace hN hM hNp hMp (-a) (-b) (even_neg_add a b hab)
      (liftedFaceVertex hN hM hNp hMp (shiftRV a b hab (canonicalPrimalLift v))) = v
    rw [translatePrimalFace_projects, shiftRV_shiftRV a b hab (even_neg_add a b hab),
      lifted_canonical]
  right_inv v := by
    change translatePrimalFace hN hM hNp hMp a b hab
      (liftedFaceVertex hN hM hNp hMp (shiftRV (-a) (-b) (even_neg_add a b hab)
        (canonicalPrimalLift v))) = v
    rw [translatePrimalFace_projects, shiftRV_shiftRV' a b hab (even_neg_add a b hab),
      lifted_canonical]

theorem translatePrimalFace_edge (e : Fin N × Fin M) :
    s(translatePrimalFace hN hM hNp hMp a b hab (faceEndpoint hN hM true e false),
      translatePrimalFace hN hM hNp hMp a b hab (faceEndpoint hN hM true e true)) =
    s(faceEndpoint hN hM true (shiftIdx hNp hMp a b e) false,
      faceEndpoint hN hM true (shiftIdx hNp hMp a b e) true) := by
  rw [← edgeLift_projects hN hM hNp hMp e false, ← edgeLift_projects hN hM hNp hMp e true,
    translatePrimalFace_projects, translatePrimalFace_projects]
  have h := liftedFaceEndpoints_eq hN hM hNp hMp (shiftRV a b hab (edgeLift e false))
    (shiftRV a b hab (edgeLift e true)) ((shiftRV_adj a b hab).2 (edgeLift_adj e))
  rw [liftedEdgeIndex_shift, edgeLift_index] at h
  exact h

theorem diamondOpen_translate_adj_iff (A : RCConfig N M) {u v : FaceVertex N M true} :
    (diamondOpenGraph hN hM true A).Adj (translatePrimalFace hN hM hNp hMp a b hab u)
      (translatePrimalFace hN hM hNp hMp a b hab v) ↔
    (diamondOpenGraph hN hM true (translRC hNp hMp a b A)).Adj u v := by
  have hinj : Function.Injective (translatePrimalFace hN hM hNp hMp a b hab) :=
    (translatePrimalFaceEquiv hN hM hNp hMp a b hab).injective
  unfold diamondOpenGraph
  rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨idx', hA, hs⟩, hne⟩
    refine ⟨⟨(shiftIdx hNp hMp a b).symm idx', ?_, ?_⟩, fun h => hne (by rw [h])⟩
    · unfold translRC
      rwa [Equiv.apply_symm_apply]
    · apply Sym2.map.injective hinj
      have hL : Sym2.map (translatePrimalFace hN hM hNp hMp a b hab) s(u, v) =
          s(faceEndpoint hN hM true idx' false, faceEndpoint hN hM true idx' true) := hs
      have h2 := translatePrimalFace_edge hN hM hNp hMp a b hab ((shiftIdx hNp hMp a b).symm idx')
      rw [Equiv.apply_symm_apply] at h2
      exact hL.trans h2.symm
  · rintro ⟨⟨idx, hA, hs⟩, hne⟩
    refine ⟨⟨shiftIdx hNp hMp a b idx, hA, ?_⟩, fun h => hne (hinj h)⟩
    have h1 : s(translatePrimalFace hN hM hNp hMp a b hab u,
        translatePrimalFace hN hM hNp hMp a b hab v) =
        Sym2.map (translatePrimalFace hN hM hNp hMp a b hab) s(u, v) := rfl
    rw [h1, hs]
    exact translatePrimalFace_edge hN hM hNp hMp a b hab idx

/-- Translation is an isomorphism of the actual open primal graphs. -/
def translateIso (A : RCConfig N M) :
    diamondOpenGraph hN hM true (translRC hNp hMp a b A) ≃g diamondOpenGraph hN hM true A where
  toEquiv := translatePrimalFaceEquiv hN hM hNp hMp a b hab
  map_rel_iff' := by
    intro u v
    exact diamondOpen_translate_adj_iff hN hM hNp hMp a b hab A

include hab in
theorem clusterCount_translate (A : RCConfig N M) :
    clusterCount hN hM true (translRC hNp hMp a b A) = clusterCount hN hM true A :=
  Nat.card_congr (translateIso hN hM hNp hMp a b hab A).connectedComponentEquiv

theorem periodicShift_neg (hp : 0 < N) (a : ℤ) : periodicShift hp (-a) = (periodicShift hp a).symm := by
  refine Equiv.ext fun j => ?_
  show periodicCoordinate hp ((j.val : ℤ) + -a) = periodicCoordinate hp ((j.val : ℤ) - a)
  rw [sub_eq_add_neg]

theorem openCount_translate (A : RCConfig N M) :
    openCount (translRC hNp hMp a b A) = openCount A := by
  unfold openCount
  apply Finset.card_equiv (shiftIdx hNp hMp a b)
  intro v
  rw [Finset.mem_filter, Finset.mem_filter]
  simp [translRC]

theorem closedCount_translate (A : RCConfig N M) :
    closedCount (translRC hNp hMp a b A) = closedCount A := by
  unfold closedCount
  apply Finset.card_equiv (shiftIdx hNp hMp a b)
  intro v
  rw [Finset.mem_filter, Finset.mem_filter]
  simp [translRC]

include hab in
theorem torusRCWeight_translate (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusRCWeight hN hM q (translRC hNp hMp a b A) = torusRCWeight hN hM q A := by
  rw [torusRCWeight, torusRCWeight, openCount_translate hNp hMp a b, closedCount_translate hNp hMp a b,
    clusterCount_translate hN hM hNp hMp a b hab]

/-- Translation as an equivalence of configurations. -/
def translRCEquiv : RCConfig N M ≃ RCConfig N M where
  toFun := translRC hNp hMp a b
  invFun := translRC hNp hMp (-a) (-b)
  left_inv A := by
    funext v
    change A (shiftIdx hNp hMp a b (shiftIdx hNp hMp (-a) (-b) v)) = A v
    have : shiftIdx hNp hMp (-a) (-b) = (shiftIdx hNp hMp a b).symm := by
      unfold shiftIdx
      rw [periodicShift_neg, periodicShift_neg]
      rfl
    rw [this, Equiv.apply_symm_apply]
  right_inv A := by
    funext v
    change A (shiftIdx hNp hMp (-a) (-b) (shiftIdx hNp hMp a b v)) = A v
    have : shiftIdx hNp hMp (-a) (-b) = (shiftIdx hNp hMp a b).symm := by
      unfold shiftIdx
      rw [periodicShift_neg, periodicShift_neg]
      rfl
    rw [this, Equiv.symm_apply_apply]

include hab in
theorem torusRCMass_translate (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusRCMass hN hM q (translRC hNp hMp a b A) = torusRCMass hN hM q A := by
  unfold torusRCMass
  rw [torusRCWeight_translate hN hM hNp hMp a b hab]

include hab in
/-- **Translation invariance** of the torus law under colour-preserving translations. -/
theorem torusRCProbability_translate (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q (translRC hNp hMp a b ⁻¹' E) = torusRCProbability hN hM q E := by
  rw [torusRCProbability_eq_sum, torusRCProbability_eq_sum]
  calc _ = ∑ A, E.indicator (torusRCMass hN hM q) (translRCEquiv hNp hMp a b A) := by
        apply Finset.sum_congr rfl
        intro A _
        change (translRC hNp hMp a b ⁻¹' E).indicator (torusRCMass hN hM q) A =
          E.indicator (torusRCMass hN hM q) (translRC hNp hMp a b A)
        by_cases h : A ∈ translRC hNp hMp a b ⁻¹' E
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show translRC hNp hMp a b A ∈ E from h),
            torusRCMass_translate hN hM hNp hMp a b hab]
        · rw [Set.indicator_of_notMem h,
            Set.indicator_of_notMem (show translRC hNp hMp a b A ∉ E from h)]
    _ = _ := Equiv.sum_comp (translRCEquiv hNp hMp a b) (E.indicator (torusRCMass hN hM q))

end Faces

theorem strip_adj_shift (hNp : 0 < N) (hMp : 0 < M) (a b : ℤ) (hab : Even (a + b))
    (A : RCConfig N M) {α β α' β' : ℤ} (hα : α = α' + a) (hβ : β = β' + a)
    (u v : RotatedVertex) :
    (liftedStripGraph hNp hMp A α β).Adj (shiftRV a b hab u) (shiftRV a b hab v) ↔
      (liftedStripGraph hNp hMp (translRC hNp hMp a b A) α' β').Adj u v := by
  subst hα hβ
  change (rotatedLattice.Adj (shiftRV a b hab u) (shiftRV a b hab v) ∧
      A (liftedEdgeIndex hNp hMp (shiftRV a b hab u) (shiftRV a b hab v)) = true ∧
      (α' + a ≤ u.val.1 + a ∧ u.val.1 + a ≤ β' + a) ∧
      (α' + a ≤ v.val.1 + a ∧ v.val.1 + a ≤ β' + a)) ↔
    (rotatedLattice.Adj u v ∧ translRC hNp hMp a b A (liftedEdgeIndex hNp hMp u v) = true ∧
      (α' ≤ u.val.1 ∧ u.val.1 ≤ β') ∧ (α' ≤ v.val.1 ∧ v.val.1 ≤ β'))
  rw [shiftRV_adj, liftedEdgeIndex_shift]
  change _ ↔ rotatedLattice.Adj u v ∧ A (shiftIdx hNp hMp a b (liftedEdgeIndex hNp hMp u v)) = true ∧ _
  constructor
  · rintro ⟨h1, h2, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
    exact ⟨h1, h2, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  · rintro ⟨h1, h2, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
    exact ⟨h1, h2, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- Translation of the lifted lattice as an equivalence. -/
def shiftRVEquiv (a b : ℤ) (hab : Even (a + b)) : RotatedVertex ≃ RotatedVertex where
  toFun := shiftRV a b hab
  invFun := shiftRV (-a) (-b) (even_neg_add a b hab)
  left_inv := shiftRV_shiftRV a b hab (even_neg_add a b hab)
  right_inv := shiftRV_shiftRV' a b hab (even_neg_add a b hab)

/-- The strip graph of the translated configuration is isomorphic to the translated strip graph. -/
def stripIso (hNp : 0 < N) (hMp : 0 < M) (a b : ℤ) (hab : Even (a + b)) (A : RCConfig N M)
    {α β α' β' : ℤ} (hα : α = α' + a) (hβ : β = β' + a) :
    liftedStripGraph hNp hMp (translRC hNp hMp a b A) α' β' ≃g liftedStripGraph hNp hMp A α β where
  toEquiv := shiftRVEquiv a b hab
  map_rel_iff' := by
    intro u v
    exact strip_adj_shift hNp hMp a b hab A hα hβ u v

/-- A vertical crossing at offset `(a, b)` of `A` is a vertical crossing at the origin of the
translated configuration. -/
theorem vCross_translate (hNp : 0 < N) (hMp : 0 < M) (n : ℕ) (a b : ℤ) (hab : Even (a + b))
    (A : RCConfig N M) (h : vCross hNp hMp n a b A) :
    vCross hNp hMp n 0 0 (translRC hNp hMp a b A) := by
  obtain ⟨u, v, hu, hv, w, hw⟩ := h
  let iso := stripIso hNp hMp a b hab A (α := a) (β := a + 3 * (n : ℤ)) (α' := 0)
    (β' := 0 + 3 * (n : ℤ)) (by ring) (by ring)
  let w' := w.map iso.symm.toHom
  refine ⟨iso.symm u, iso.symm v, ?_, ?_, w', ?_⟩
  · change u.val.2 + -b = 0; omega
  · change v.val.2 + -b = 0 + n; omega
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hz
    have := hw z0 hz0
    change 0 ≤ z0.val.2 + -b ∧ z0.val.2 + -b ≤ 0 + n
    omega

/-- A vertical crossing at an offset of the right parity is no more likely than at the origin. -/
theorem prob_vCross_le (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (n : ℕ) (a b : ℤ) (hab : Even (a + b)) :
    torusRCProbability hN hM q {A | vCross hNp hMp n a b A} ≤
      torusRCProbability hN hM q {A | vCross hNp hMp n 0 0 A} := by
  have hsub : {A | vCross hNp hMp n a b A} ⊆
      translRC hNp hMp a b ⁻¹' {A | vCross hNp hMp n 0 0 A} :=
    fun A hA => vCross_translate hNp hMp n a b hab A hA
  calc _ ≤ torusRCProbability hN hM q (translRC hNp hMp a b ⁻¹' {A | vCross hNp hMp n 0 0 A}) :=
        torusRCProbability_mono hN hM q hsub
    _ = _ := torusRCProbability_translate hN hM hNp hMp a b hab q _

end PottsDiscontinuity.TorusCrossing
