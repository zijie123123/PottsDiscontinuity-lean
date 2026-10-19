module

public import PottsDiscontinuity.CorrLength.CorrelationRate

/-!
# Free limit and connection rate on the rotated lattice

The rotated configuration space is transported through the graph isomorphism
with the square lattice. Image-box laws are the corresponding transported free
finite-box laws. The free-box uniqueness theorem therefore gives the same limit
along every nested exhaustive sequence of image boxes.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.CorrLength

open PottsDiscontinuity.FK

noncomputable section

/-- Edge configurations on the rotated lattice `L`. -/
abbrev RotatedConfiguration := rotatedLattice.edgeSet → Bool

/-- The finite rotated domain whose image under the lattice isomorphism is the
square box centered at `c` with radius `r`. -/
def rotatedImageBoxDomain (c : LatticeVertex) (r : ℕ) : Set RotatedVertex :=
  {v | rotatedToSquareVertex v ∈ latticeBox c r}

/-- The induced finite graph on an image box in the rotated lattice. -/
def rotatedImageBoxGraph (c : LatticeVertex) (r : ℕ) :=
  rotatedLattice.induce (rotatedImageBoxDomain c r)

/-- The induced graph on a rotated image box is isomorphic to its square-box
image. -/
def rotatedImageBoxGraphIso (c : LatticeVertex) (r : ℕ) :
    rotatedImageBoxGraph c r ≃g boxGraph c r where
  toEquiv :=
    { toFun := fun v => ⟨rotatedToSquareVertex v.1, v.2⟩
      invFun := fun v => ⟨squareToRotatedVertex v.1, by
        change rotatedToSquareVertex (squareToRotatedVertex v.1) ∈ latticeBox c r
        simp⟩
      left_inv := by
        intro v
        apply Subtype.ext
        exact squareToRotated_rotatedToSquare v.1
      right_inv := by
        intro v
        apply Subtype.ext
        exact rotatedToSquare_squareToRotated v.1 }
  map_rel_iff' := by
    intro u v
    change squareLattice.Adj (rotatedToSquareVertex u.1) (rotatedToSquareVertex v.1) ↔
      rotatedLattice.Adj u.1 v.1
    exact (rotatedLattice_adj_iff_square u.1 v.1).symm

local instance rotatedImageBoxVertexFintype (c : LatticeVertex) (r : ℕ) :
    Fintype {v : RotatedVertex // v ∈ rotatedImageBoxDomain c r} :=
  Fintype.ofEquiv (BoxVertex c r) (rotatedImageBoxGraphIso c r).toEquiv.symm

local instance rotatedImageBoxEdgeFintype (c : LatticeVertex) (r : ℕ) :
    Fintype (rotatedImageBoxGraph c r).edgeSet := Fintype.ofFinite _

local instance rotatedImageBoxEdgeDecidableEq (c : LatticeVertex) (r : ℕ) :
    DecidableEq (rotatedImageBoxGraph c r).edgeSet := Classical.decEq _

/-- Coordinate transport of whole-lattice configurations from `ℤ²` to `L`. -/
def rotatedConfigurationHomeomorph :
    LatticeConfiguration ≃ₜ RotatedConfiguration :=
  Homeomorph.piCongrLeft (Y := fun _ : rotatedLattice.edgeSet => Bool)
    (SimpleGraph.Iso.mapEdgeSet rotatedLatticeIso.symm)

@[simp] theorem rotatedConfigurationHomeomorph_apply
    (ω : LatticeConfiguration) (e : rotatedLattice.edgeSet) :
    rotatedConfigurationHomeomorph ω e =
      ω (SimpleGraph.Iso.mapEdgeSet rotatedLatticeIso e) := by
  simp [rotatedConfigurationHomeomorph, Homeomorph.piCongrLeft,
    Equiv.piCongrLeft, SimpleGraph.Iso.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet]

/-- The free random-cluster measure on `L`, defined by transporting the unique
square-lattice free-box limit through the graph isomorphism. -/
def rotatedFreeBoxLimit (θ : Parameters) : ProbabilityMeasure RotatedConfiguration :=
  ProbabilityMeasure.map (Classical.choose (freeBoxLimit_existsUnique θ))
    rotatedConfigurationHomeomorph

/-- The rotated event of connection is the pullback of the finite-witness
connection event under the lattice graph isomorphism. -/
def rotatedConnectionEvent (u v : RotatedVertex) : Set RotatedConfiguration :=
  (rotatedConfigurationHomeomorph.symm) ⁻¹'
    connectionEvent (rotatedVertexEquiv u) (rotatedVertexEquiv v)

theorem rotatedConnectionEvent_isMeasurableSet (u v : RotatedVertex) :
    MeasurableSet (rotatedConnectionEvent u v) :=
  (connectionEvent_isMeasurableSet (rotatedVertexEquiv u) (rotatedVertexEquiv v)).preimage
    rotatedConfigurationHomeomorph.symm.continuous_toFun.measurable

/-- Connection probabilities are preserved by the rotated-lattice isomorphism. -/
theorem rotatedFreeBoxLimit_connectionProbability (θ : Parameters)
    (u v : RotatedVertex) :
    rotatedFreeBoxLimit θ (rotatedConnectionEvent u v) =
      Classical.choose (freeBoxLimit_existsUnique θ)
        (connectionEvent (rotatedVertexEquiv u) (rotatedVertexEquiv v)) := by
  let ν : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (freeBoxLimit_existsUnique θ)
  have hpre : rotatedConfigurationHomeomorph.toFun ⁻¹' rotatedConnectionEvent u v =
      connectionEvent (rotatedVertexEquiv u) (rotatedVertexEquiv v) := by
    ext ω
    simp [rotatedConnectionEvent]
  have hmap := ProbabilityMeasure.map_apply ν
      (rotatedConfigurationHomeomorph.continuous_toFun.measurable.aemeasurable)
      (rotatedConnectionEvent_isMeasurableSet u v)
  rw [hpre] at hmap
  simpa only [rotatedFreeBoxLimit, ν, Prod.forall, Equiv.toFun_as_coe,
    Homeomorph.coe_toEquiv] using hmap

/-- The origin of `L`. -/
def rotatedLatticeOrigin : RotatedVertex :=
  ⟨(0, 0), ⟨0, by simp⟩⟩

/-- The point `(0,2n)` on `L`, whose square-lattice image is `(n,n)`. -/
def rotatedDiagonalSite (n : ℕ) : RotatedVertex :=
  ⟨(0, 2 * (n : ℤ)), ⟨(n : ℤ), by ring⟩⟩

@[simp] theorem rotatedVertexEquiv_origin :
    rotatedVertexEquiv rotatedLatticeOrigin = (0, 0) := by
  simp [rotatedVertexEquiv, rotatedLatticeOrigin, rotatedToSquareVertex]

@[simp] theorem rotatedVertexEquiv_diagonalSite (n : ℕ) :
    rotatedVertexEquiv (rotatedDiagonalSite n) = ((n : ℤ), (n : ℤ)) := by
  exact rotatedVertexEquiv_apply_origin_to_even_site n

/-- The rotated free connection probability from `0` to `(0,2n)`. -/
def rotatedDiagonalConnectionProbability (θ : Parameters) (n : ℕ) : NNReal :=
  rotatedFreeBoxLimit θ
    (rotatedConnectionEvent rotatedLatticeOrigin (rotatedDiagonalSite n))

theorem rotatedDiagonalConnectionProbability_eq (θ : Parameters) (n : ℕ) :
    rotatedDiagonalConnectionProbability θ n =
      Classical.choose (freeBoxLimit_existsUnique θ)
        (connectionEvent (0, 0) ((n : ℤ), (n : ℤ))) := by
  simp only [rotatedDiagonalConnectionProbability, rotatedFreeBoxLimit_connectionProbability,
    Prod.forall, rotatedVertexEquiv_origin, rotatedVertexEquiv_diagonalSite]

/-- On the rotated lattice, the exponent per graph-distance `2n` has the same
limit as the frozen diagonal-site sequence. -/
theorem rotated_correlation_rate_exists (θ : Parameters) :
    ∃ aInf : ℝ, 0 ≤ aInf ∧
      Tendsto (fun n : ℕ =>
        -Real.log ((rotatedDiagonalConnectionProbability θ n : NNReal) : ℝ) /
          ((2 * n : ℕ) : ℝ)) atTop (𝓝 (aInf / 2)) ∧
      Tendsto (fun n : ℕ =>
        -Real.log (((Classical.choose (freeBoxLimit_existsUnique θ) :
          ProbabilityMeasure LatticeConfiguration).toMeasure.real
          (connectionEvent (0, 0) (PottsDiscontinuity.diagonalSite n)))) /
            (n : ℝ)) atTop (𝓝 (aInf / 2)) := by
  let ν : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (freeBoxLimit_existsUnique θ)
  have hweak : Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n) atTop
      (𝓝 ν) :=
    (Classical.choose_spec (freeBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive
  have hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 ν.toMeasure :=
    isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν hweak
  obtain ⟨aInf, haInf, hdiag⟩ := diagonalSite_correlation_rate_exists θ ν.toMeasure hμ
  have hdouble : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have hdiagDouble := hdiag.comp hdouble
  have hterms (n : ℕ) :
      -Real.log ((rotatedDiagonalConnectionProbability θ n : NNReal) : ℝ) /
          ((2 * n : ℕ) : ℝ) =
        -Real.log (ν.toMeasure.real (connectionEvent (0, 0)
          (PottsDiscontinuity.diagonalSite (2 * n)))) /
            ((2 * n : ℕ) : ℝ) := by
    rw [rotatedDiagonalConnectionProbability_eq]
    simp only [Prod.forall, Nat.cast_mul, Nat.cast_ofNat, diagonalSite_even,
      ProbabilityMeasure.measureReal_eq_coe_coeFn, ν]
  have hrot : Tendsto (fun n : ℕ =>
      -Real.log ((rotatedDiagonalConnectionProbability θ n : NNReal) : ℝ) /
        ((2 * n : ℕ) : ℝ)) atTop (𝓝 (aInf / 2)) := by
    refine hdiagDouble.congr' ?_
    filter_upwards with n
    exact (hterms n).symm
  refine ⟨aInf, haInf, hrot, ?_⟩
  simpa only [ν, Prod.forall, ProbabilityMeasure.measureReal_eq_coe_coeFn] using hdiag

/-- The rotated-lattice rate agrees with the diagonal-site rate for any
measure satisfying the frozen free-limit characterization. -/
theorem rotated_correlation_rate_exists_for_limit (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) :
    ∃ aInf : ℝ, 0 ≤ aInf ∧
      Tendsto (fun n : ℕ =>
        -Real.log ((rotatedDiagonalConnectionProbability θ n : NNReal) : ℝ) /
          ((2 * n : ℕ) : ℝ)) atTop (𝓝 (aInf / 2)) ∧
      Tendsto (fun n : ℕ =>
        -Real.log (μ.real (connectionEvent (0, 0)
          (PottsDiscontinuity.diagonalSite n))) / (n : ℝ))
        atTop (𝓝 (aInf / 2)) := by
  obtain ⟨aInf, haInf, hrot, hdiag⟩ := rotated_correlation_rate_exists θ
  let ν : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (freeBoxLimit_existsUnique θ)
  have hweak : Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n) atTop
      (𝓝 ν) :=
    (Classical.choose_spec (freeBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive
  have hν : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 ν.toMeasure :=
    isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν hweak
  have hEq : μ = ν.toMeasure :=
    PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 0 μ ν.toMeasure hμ hν
  have hdiagμ : Tendsto (fun n : ℕ =>
      -Real.log (μ.real (connectionEvent (0, 0)
        (PottsDiscontinuity.diagonalSite n))) / (n : ℝ))
      atTop (𝓝 (aInf / 2)) := by
    refine hdiag.congr' ?_
    filter_upwards with n
    rw [hEq]
  exact ⟨aInf, haInf, hrot, hdiagμ⟩

end

end PottsDiscontinuity.CorrLength
