module

public import PottsDiscontinuity.FK.PositiveAssociation
public import PottsDiscontinuity.SixVertex.InfinityDescent
public import PottsDiscontinuity.TorusLoops.FiniteEnergy

/-!
# The fixed FK graph of the cut diamond rectangle

The open rectangle graph from `RectangleCrossings` is the open subgraph of this
fixed finite graph. Interior indexed diamond edges are in bijection with its
simple-graph edges; excluding both seams makes the coordinatewise maximum of
the endpoints recover the original medial index.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus PottsDiscontinuity.SixVertex

variable {N M : ℕ}

/-- Medial indices whose indexed edge survives both rectangle cuts. -/
abbrev RectangleEdgeIndex := {v : Fin N × Fin M // v.1.val ≠ 0 ∧ v.2.val ≠ 0}

/-- The fixed simple graph containing all edges that survive the two cuts. -/
def rectangleBaseGraph (hN : Even N) (hM : Even M) :
    SimpleGraph (FaceVertex N M true) :=
  SimpleGraph.fromEdgeSet {p | ∃ v : RectangleEdgeIndex (N := N) (M := M),
    p = Sym2.mk (faceEndpoint hN hM true v.val false)
      (faceEndpoint hN hM true v.val true)}

/-- Indexed torus edges deleted by the two rectangle seams. -/
def rectangleSeamIndices : Finset (Fin N × Fin M) :=
  Finset.univ.filter (fun v => v.1.val = 0 ∨ v.2.val = 0)

/-- The ordinary FK parameter pair whose edge parameter is the critical torus
edge probability and whose cluster parameter is `q`. -/
noncomputable def rectangleFKParameters (q : Set.Ici (1 : ℝ)) : FK.Parameters :=
  ⟨q.val, q.property,
    ⟨(rcCriticalParameter q).val,
      PottsDiscontinuity.TorusRC.criticalParameter_pos q,
      PottsDiscontinuity.TorusRC.criticalParameter_lt_one q⟩⟩

private theorem rectangleEndpointXFalse (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v false).val.1.val =
      if checker v then v.1.val else (prv v.1).val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointXTrue (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v true).val.1.val =
      if checker v then (prv v.1).val else v.1.val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointYFalse (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v false).val.2.val = v.2.val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointYTrue (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v true).val.2.val = (prv v.2).val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointMaxX (hN : Even N) (hM : Even M)
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    max (faceEndpoint hN hM true v.val false).val.1.val
        (faceEndpoint hN hM true v.val true).val.1.val = v.val.1.val := by
  let : NeZero N := v.val.1.neZero
  have hfin : v.val.1 ≠ 0 := by
    intro hz
    apply v.property.1
    simpa using congrArg Fin.val hz
  rw [rectangleEndpointXFalse, rectangleEndpointXTrue]
  cases checker v.val <;> simp <;>
    exact Fin.one_le_of_ne_zero hfin

private theorem rectangleEndpointMaxY (hN : Even N) (hM : Even M)
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    max (faceEndpoint hN hM true v.val false).val.2.val
        (faceEndpoint hN hM true v.val true).val.2.val = v.val.2.val := by
  have hp := prv_val_of_pos v.val.2 (Nat.pos_of_ne_zero v.property.2)
  rw [rectangleEndpointYFalse, rectangleEndpointYTrue]
  omega

private theorem rectangleEdgeIndex_endpoints_injective (hN : Even N) (hM : Even M)
    (v w : RectangleEdgeIndex (N := N) (M := M))
    (he : Sym2.mk (faceEndpoint hN hM true v.val false)
        (faceEndpoint hN hM true v.val true) =
      Sym2.mk (faceEndpoint hN hM true w.val false)
        (faceEndpoint hN hM true w.val true)) : v = w := by
  rcases Sym2.eq_iff.mp he with ⟨hff, htt⟩ | ⟨hft, htf⟩
  · have hx : v.val.1.val = w.val.1.val := by
      calc
        v.val.1.val = max (faceEndpoint hN hM true v.val false).val.1.val
            (faceEndpoint hN hM true v.val true).val.1.val :=
              (rectangleEndpointMaxX hN hM v).symm
        _ = max (faceEndpoint hN hM true w.val false).val.1.val
            (faceEndpoint hN hM true w.val true).val.1.val := by rw [hff, htt]
        _ = w.val.1.val := rectangleEndpointMaxX hN hM w
    have hy : v.val.2.val = w.val.2.val := by
      calc
        v.val.2.val = max (faceEndpoint hN hM true v.val false).val.2.val
            (faceEndpoint hN hM true v.val true).val.2.val :=
              (rectangleEndpointMaxY hN hM v).symm
        _ = max (faceEndpoint hN hM true w.val false).val.2.val
            (faceEndpoint hN hM true w.val true).val.2.val := by rw [hff, htt]
        _ = w.val.2.val := rectangleEndpointMaxY hN hM w
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> assumption
  · have hx : v.val.1.val = w.val.1.val := by
      calc
        v.val.1.val = max (faceEndpoint hN hM true v.val false).val.1.val
            (faceEndpoint hN hM true v.val true).val.1.val :=
              (rectangleEndpointMaxX hN hM v).symm
        _ = max (faceEndpoint hN hM true w.val false).val.1.val
            (faceEndpoint hN hM true w.val true).val.1.val := by rw [hft, htf, Nat.max_comm]
        _ = w.val.1.val := rectangleEndpointMaxX hN hM w
    have hy : v.val.2.val = w.val.2.val := by
      calc
        v.val.2.val = max (faceEndpoint hN hM true v.val false).val.2.val
            (faceEndpoint hN hM true v.val true).val.2.val :=
              (rectangleEndpointMaxY hN hM v).symm
        _ = max (faceEndpoint hN hM true w.val false).val.2.val
            (faceEndpoint hN hM true w.val true).val.2.val := by rw [hft, htf, Nat.max_comm]
        _ = w.val.2.val := rectangleEndpointMaxY hN hM w
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> assumption

private theorem rectangleEndpoints_ne (hN : Even N) (hM : Even M)
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    faceEndpoint hN hM true v.val false ≠ faceEndpoint hN hM true v.val true := by
  intro he
  have hx := congrArg (fun x : FaceVertex N M true => x.val.1.val) he
  rw [rectangleEndpointXFalse, rectangleEndpointXTrue] at hx
  have hi := Nat.pos_of_ne_zero v.property.1
  have hp := prv_val_of_pos v.val.1 hi
  cases hc : checker v.val
  · simp only [hc, Bool.false_eq_true, ite_false] at hx
    rw [hp] at hx
    omega
  · simp only [hc, ite_true] at hx
    rw [hp] at hx
    omega

/-- The medial index embeds into the unordered edges of the fixed rectangle graph. -/
def rectangleBaseEdgeEmbedding (hN : Even N) (hM : Even M) :
    RectangleEdgeIndex (N := N) (M := M) ↪ (rectangleBaseGraph hN hM).edgeSet where
  toFun v := ⟨Sym2.mk (faceEndpoint hN hM true v.val false)
      (faceEndpoint hN hM true v.val true), by
    rw [rectangleBaseGraph, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨⟨v, rfl⟩, ?_⟩
    intro hd
    simp only [Sym2.mem_diagSet, Sym2.mk_isDiag_iff] at hd
    exact rectangleEndpoints_ne hN hM v hd
  ⟩
  inj' := by
    intro v w hvw
    apply rectangleEdgeIndex_endpoints_injective hN hM
    exact congrArg Subtype.val hvw

/-- Every edge of the rectangle graph is represented by a unique interior
medial index. -/
noncomputable def rectangleBaseEdgeEquiv (hN : Even N) (hM : Even M) :
    RectangleEdgeIndex (N := N) (M := M) ≃ (rectangleBaseGraph hN hM).edgeSet :=
  Equiv.ofBijective (rectangleBaseEdgeEmbedding hN hM) ⟨
    (rectangleBaseEdgeEmbedding hN hM).injective,
    by
      intro e
      have he := e.property
      simp only [rectangleBaseGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
      rcases he.1 with ⟨v, hv⟩
      exact ⟨v, Subtype.ext hv.symm⟩⟩

/-- The rectangle configuration induced by the interior states of a torus
configuration. -/
noncomputable def rectangleConfigurationOfRC (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : FK.Configuration (rectangleBaseGraph hN hM) :=
  (Finset.univ.filter (fun v : RectangleEdgeIndex => A v.val = true)).map
    (rectangleBaseEdgeEmbedding hN hM)

@[simp] theorem mem_rectangleConfigurationOfRC
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    rectangleBaseEdgeEmbedding hN hM v ∈ rectangleConfigurationOfRC hN hM A ↔
      A v.val = true := by
  classical
  rw [rectangleConfigurationOfRC, Finset.mem_map]
  constructor
  · rintro ⟨w, hw, hew⟩
    have hvw := (rectangleBaseEdgeEmbedding hN hM).injective hew
    subst w
    exact (Finset.mem_filter.mp hw).2
  · intro hv
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

/-- Extend a rectangle FK configuration to the full indexed torus by keeping
all seam states closed. -/
noncomputable def rectangleRCConfigOfConfiguration (hN : Even N) (hM : Even M)
    (C : FK.Configuration (rectangleBaseGraph hN hM)) : RCConfig N M := by
  classical
  exact fun v => if h : v.1.val ≠ 0 ∧ v.2.val ≠ 0 then
    decide (rectangleBaseEdgeEmbedding hN hM ⟨v, h⟩ ∈ C) else false

@[simp] theorem rectangleRCConfigOfConfiguration_interior
    (hN : Even N) (hM : Even M)
    (C : FK.Configuration (rectangleBaseGraph hN hM))
    (v : RectangleEdgeIndex (N := N) (M := M)) :
    rectangleRCConfigOfConfiguration hN hM C v.val =
      decide (rectangleBaseEdgeEmbedding hN hM v ∈ C) := by
  classical
  simp [rectangleRCConfigOfConfiguration, v.property]

theorem rectangleRCConfigOfConfiguration_closedOnSeams
    (hN : Even N) (hM : Even M)
    (C : FK.Configuration (rectangleBaseGraph hN hM))
    (v : Fin N × Fin M) (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    rectangleRCConfigOfConfiguration hN hM C v = false := by
  classical
  by_cases hi : v.1.val ≠ 0 ∧ v.2.val ≠ 0
  · rcases hseam with hx | hy
    · exact (hi.1 hx).elim
    · exact (hi.2 hy).elim
  · simp [rectangleRCConfigOfConfiguration, hi]

theorem rectangleConfigurationOfRC_rectangleRCConfigOfConfiguration
    (hN : Even N) (hM : Even M)
    (C : FK.Configuration (rectangleBaseGraph hN hM)) :
    rectangleConfigurationOfRC hN hM
      (rectangleRCConfigOfConfiguration hN hM C) = C := by
  classical
  ext e
  let v := (rectangleBaseEdgeEquiv hN hM).symm e
  have hev : rectangleBaseEdgeEmbedding hN hM v = e :=
    (rectangleBaseEdgeEquiv hN hM).apply_symm_apply e
  rw [← hev, mem_rectangleConfigurationOfRC,
    rectangleRCConfigOfConfiguration_interior]
  simp

theorem rectangleRCConfigOfConfiguration_rectangleConfigurationOfRC
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    rectangleRCConfigOfConfiguration hN hM (rectangleConfigurationOfRC hN hM A) = A := by
  funext v
  by_cases hs : v.1.val = 0 ∨ v.2.val = 0
  · rw [rectangleRCConfigOfConfiguration_closedOnSeams hN hM _ v hs, hclosed v hs]
  · have hx : v.1.val ≠ 0 := by
      intro hz
      exact hs (Or.inl hz)
    have hy : v.2.val ≠ 0 := by
      intro hz
      exact hs (Or.inr hz)
    let w : RectangleEdgeIndex (N := N) (M := M) := ⟨v, hx, hy⟩
    change rectangleRCConfigOfConfiguration hN hM
      (rectangleConfigurationOfRC hN hM A) w.val = A w.val
    rw [rectangleRCConfigOfConfiguration_interior]
    cases hav : A v <;> simp [rectangleConfigurationOfRC, hav, w]

theorem rectangleOpenEdges_eq (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    FK.openEdges (rectangleBaseGraph hN hM) (rectangleConfigurationOfRC hN hM A) =
      {p | ∃ v : RectangleEdgeIndex (N := N) (M := M), A v.val = true ∧
        p = Sym2.mk (faceEndpoint hN hM true v.val false)
          (faceEndpoint hN hM true v.val true)} := by
  classical
  ext p
  constructor
  · rintro ⟨e, he, rfl⟩
    rcases Finset.mem_map.mp he with ⟨v, hv, hev⟩
    exact ⟨v, (Finset.mem_filter.mp hv).2, (congrArg Subtype.val hev).symm⟩
  · rintro ⟨v, hv, hp⟩
    refine ⟨rectangleBaseEdgeEmbedding hN hM v,
      (mem_rectangleConfigurationOfRC hN hM A v).2 hv, ?_⟩
    change Sym2.mk _ _ = p
    exact hp.symm

/-- Closing the two indexed seams makes the torus primal open graph exactly the
FK open graph of the cut rectangle. -/
theorem rectangleOpenGraph_eq_diamondOpenGraph_closedOnSeams
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    FK.openGraph (rectangleBaseGraph hN hM) (rectangleConfigurationOfRC hN hM A) =
      diamondOpenGraph hN hM true A := by
  ext u w
  rw [FK.openGraph_adj, diamondOpenGraph, SimpleGraph.fromEdgeSet_adj,
    rectangleOpenEdges_eq]
  constructor
  · rintro ⟨v, hv, hp⟩
    refine ⟨⟨v.val, hv, hp⟩, ?_⟩
    intro huw
    have hdiag : (Sym2.mk
        (faceEndpoint hN hM true v.val false)
        (faceEndpoint hN hM true v.val true)).IsDiag := by
      have hd : (Sym2.mk u w).IsDiag := Sym2.mk_isDiag_iff.mpr huw
      rw [← hp]
      exact hd
    exact rectangleEndpoints_ne hN hM v (Sym2.mk_isDiag_iff.mp hdiag)
  · rintro ⟨⟨v, hv, hp⟩, _⟩
    have hx : v.1.val ≠ 0 := by
      intro hz
      have hc := hclosed v (Or.inl hz)
      rw [hc] at hv
      contradiction
    have hy : v.2.val ≠ 0 := by
      intro hz
      have hc := hclosed v (Or.inr hz)
      rw [hc] at hv
      contradiction
    exact ⟨⟨v, hx, hy⟩, hv, hp⟩

theorem rectangleConfiguration_card_eq_openCount
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    (rectangleConfigurationOfRC hN hM A).card = openCount A := by
  classical
  let I : Finset (RectangleEdgeIndex (N := N) (M := M)) :=
    Finset.univ.filter (fun v => A v.val = true)
  let O : Finset (Fin N × Fin M) := Finset.univ.filter (fun v => A v = true)
  have hO : O = I.image Subtype.val := by
    ext v
    simp only [O, I, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hv
      have hinterior : v.1.val ≠ 0 ∧ v.2.val ≠ 0 := by
        by_contra hnot
        have hseam : v.1.val = 0 ∨ v.2.val = 0 := by
          by_contra hseam
          exact hnot ⟨by intro hz; exact hseam (Or.inl hz),
            by intro hz; exact hseam (Or.inr hz)⟩
        have hclosedv := hclosed v hseam
        rw [hclosedv] at hv
        contradiction
      exact ⟨⟨v, hinterior⟩, hv, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact hw
  have hcardI : (rectangleConfigurationOfRC hN hM A).card = I.card := by
    rw [rectangleConfigurationOfRC, Finset.card_map]
  calc
    (rectangleConfigurationOfRC hN hM A).card = I.card := hcardI
    _ = (I.image Subtype.val).card :=
      (Finset.card_image_of_injective I Subtype.val_injective).symm
    _ = O.card := by rw [← hO]
    _ = openCount A := rfl

theorem rectangleFreeComponentCount_eq_clusterCount
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    FK.componentCount (rectangleBaseGraph hN hM) (FK.BoundaryCondition.free ∅)
      (rectangleConfigurationOfRC hN hM A) = clusterCount hN hM true A := by
  rw [FK.componentCount, FK.componentSetoid_free,
    rectangleOpenGraph_eq_diamondOpenGraph_closedOnSeams hN hM A hclosed]
  rfl

theorem rectangleBaseEdgeCount_add_seamCount (hN : Even N) (hM : Even M) :
    Nat.card (rectangleBaseGraph hN hM).edgeSet +
      (rectangleSeamIndices (N := N) (M := M)).card = N * M := by
  classical
  let I : Finset (Fin N × Fin M) :=
    Finset.univ.filter (fun v => v.1.val ≠ 0 ∧ v.2.val ≠ 0)
  have hnot : Finset.univ.filter
      (fun v : Fin N × Fin M => ¬ (v.1.val ≠ 0 ∧ v.2.val ≠ 0)) =
      rectangleSeamIndices := by
    ext v
    by_cases hx : v.1.val = 0 <;> by_cases hy : v.2.val = 0 <;>
      simp [rectangleSeamIndices, hx, hy]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N × Fin M)))
    (p := fun v : Fin N × Fin M => v.1.val ≠ 0 ∧ v.2.val ≠ 0)
  rw [hnot] at hsplit
  have hindex : Fintype.card (RectangleEdgeIndex (N := N) (M := M)) = I.card := by
    simp [RectangleEdgeIndex, I, Fintype.card_subtype]
  have hedge : Nat.card (rectangleBaseGraph hN hM).edgeSet = I.card := by
    calc
      Nat.card (rectangleBaseGraph hN hM).edgeSet =
          Nat.card (RectangleEdgeIndex (N := N) (M := M)) :=
        (Nat.card_congr (rectangleBaseEdgeEquiv hN hM)).symm
      _ = Fintype.card (RectangleEdgeIndex (N := N) (M := M)) :=
        Nat.card_eq_fintype_card
      _ = I.card := hindex
  rw [hedge]
  simpa [I, Fintype.card_prod, Fintype.card_fin] using hsplit

theorem rectangleConfiguration_closedCount_eq_seam_add_freeClosedCount
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    closedCount A = (rectangleSeamIndices (N := N) (M := M)).card +
      (Nat.card (rectangleBaseGraph hN hM).edgeSet -
        (rectangleConfigurationOfRC hN hM A).card) := by
  have htotal := openCount_add_closedCount A
  have hopen := rectangleConfiguration_card_eq_openCount hN hM A hclosed
  have hsplit := rectangleBaseEdgeCount_add_seamCount hN hM
  let : Fintype (rectangleBaseGraph hN hM).edgeSet := Fintype.ofFinite _
  have hle : (rectangleConfigurationOfRC hN hM A).card ≤
      Nat.card (rectangleBaseGraph hN hM).edgeSet := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  omega

theorem torusRCWeight_eq_seamFactor_mul_rectangleFKWeight
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (A : RCConfig N M)
    (hclosed : ∀ v : Fin N × Fin M,
      v.1.val = 0 ∨ v.2.val = 0 → A v = false) :
    torusRCWeight hN hM q A =
      (1 - (rcCriticalParameter q).val) ^
          (rectangleSeamIndices (N := N) (M := M)).card *
        FK.weight (rectangleBaseGraph hN hM) (rectangleFKParameters q)
          (FK.BoundaryCondition.free ∅) (rectangleConfigurationOfRC hN hM A) := by
  rw [torusRCWeight, FK.weight]
  rw [← rectangleConfiguration_card_eq_openCount hN hM A hclosed,
    rectangleConfiguration_closedCount_eq_seam_add_freeClosedCount hN hM A hclosed,
    ← rectangleFreeComponentCount_eq_clusterCount hN hM A hclosed]
  simp only [rectangleFKParameters, FK.edgeParameter]
  rw [pow_add]
  ring

end PottsDiscontinuity.TorusLoops
