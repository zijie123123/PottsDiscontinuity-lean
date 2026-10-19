/- The box-exhaustion argument is adapted from an earlier, unpublished formalization of the planar FK model by the same author.
The endpoint weight and measure proofs are original proofs for the frozen definitions. -/
module

public import PottsDiscontinuity.Frozen.Defs.IsRCInfiniteVolumeLimit
public import PottsDiscontinuity.Infra.RCWeightBasic

/-!
# The random-cluster limits at the two edge-parameter endpoints

For every positive cluster weight and either boundary condition, the frozen finite-volume
laws at `p = 0` and `p = 1` concentrate on the constant configurations. Their cylinder limits
are the corresponding Dirac probability measures.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK

/-- The edge parameter corresponding to a deterministic Boolean edge state. -/
def endpointParameter (b : Bool) : Set.Icc (0 : ℝ) 1 :=
  if b then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩

private theorem endpoint_weight_eq_zero (V : Finset (ℤ × ℤ))
    (q : Set.Ioi (0 : ℝ)) (i : Fin 2) (b : Bool)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    (hω : ω ≠ fun _ => b) : rcWeight V (endpointParameter b) q i ω = 0 := by
  classical
  have hex : ∃ e, ω e ≠ b := by
    by_contra h
    apply hω
    funext e
    exact not_not.mp fun he => h ⟨e, he⟩
  obtain ⟨e, he⟩ := hex
  cases b with
  | false =>
      have htrue : ω e = true := by cases h : ω e <;> simp_all
      have : Nonempty {f // ω f = true} := ⟨⟨e, htrue⟩⟩
      have hn : Nat.card {f // ω f = true} ≠ 0 := Nat.card_pos.ne'
      simp [rcWeight, endpointParameter]
  | true =>
      have hfalse : ω e = false := by cases h : ω e <;> simp_all
      have : Nonempty {f // ω f = false} := ⟨⟨e, hfalse⟩⟩
      have hn : Nat.card {f // ω f = false} ≠ 0 := Nat.card_pos.ne'
      simp [rcWeight, endpointParameter]

open Classical in
/-- The frozen finite-volume law at an endpoint is a point mass. -/
theorem rcProb_endpoint (V : Finset (ℤ × ℤ)) (q : Set.Ioi (0 : ℝ))
    (i : Fin 2) (b : Bool)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    rcProb V (endpointParameter b) q i ω = if ω = (fun _ => b) then 1 else 0 := by
  classical
  have hsum : (∑ ω', rcWeight V (endpointParameter b) q i ω') =
      rcWeight V (endpointParameter b) q i (fun _ => b) := by
    apply Finset.sum_eq_single (fun _ => b)
    · intro ω' _ hω'
      exact endpoint_weight_eq_zero V q i b ω' hω'
    · simp
  have hpos : 0 < rcWeight V (endpointParameter b) q i (fun _ => b) := by
    rw [← hsum]
    exact rcWeight_denominator_pos V (endpointParameter b) q i
  by_cases hω : ω = (fun _ => b)
  · rw [ite_eq_left hω, hω]
    unfold rcProb
    rw [hsum, div_self (ne_of_gt hpos)]
  · rw [ite_eq_right hω]
    unfold rcProb
    rw [endpoint_weight_eq_zero V q i b ω hω, zero_div]

/-- Every fixed lattice vertex lies in all sufficiently large frozen boxes. -/
theorem eventually_mem_box (x : ℤ × ℤ) : ∀ᶠ n : ℕ in atTop, x ∈ box n := by
  filter_upwards [eventually_ge_atTop (max x.1.natAbs x.2.natAbs)] with n hn
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  constructor <;> constructor <;> omega

/-- Every fixed lattice edge has a lift to the induced graph on every sufficiently large box. -/
theorem eventually_edge_lift_box (e : squareLattice.edgeSet) :
    ∀ᶠ n : ℕ in atTop,
      ∃ f : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      filter_upwards [eventually_mem_box x, eventually_mem_box y] with n hx hy
      refine ⟨⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩, rfl⟩
      exact he

/-- At either endpoint, the frozen box laws converge to the deterministic infinite configuration. -/
theorem isRCInfiniteVolumeLimit_endpoint (q : Set.Ioi (0 : ℝ)) (i : Fin 2) (b : Bool) :
    IsRCInfiniteVolumeLimit (endpointParameter b) q i (Measure.dirac (fun _ => b)) := by
  classical
  constructor
  · infer_instance
  · intro A ξ
    have hA : ∀ᶠ n : ℕ in atTop, ∀ e ∈ A,
        ∃ f : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet,
          Sym2.map Subtype.val f.1 = e.1 :=
      (eventually_all_finset A).2 fun e _ => eventually_edge_lift_box e
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hA] with n hn
    symm
    rw [Finset.sum_eq_single (fun _ => b)]
    · rw [rcProb_endpoint, Measure.dirac_real_apply]
      have hiff :
          (∀ e ∈ A, ∃ f : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet,
            Sym2.map Subtype.val f.1 = e.1 ∧ b = ξ e) ↔ ∀ e ∈ A, b = ξ e := by
        constructor
        · intro h e he
          obtain ⟨f, _, hf⟩ := h e he
          exact hf
        · intro h e he
          obtain ⟨f, hf⟩ := hn e he
          exact ⟨f, hf, h e he⟩
      simp only [hiff, ite_true, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    · intro ω _ hω
      rw [rcProb_endpoint, ite_eq_right hω]
      exact ite_self _
    · simp

/-- The frozen random-cluster infinite-volume measure exists at `p = 0`, for every `q > 0`. -/
theorem exists_isRCInfiniteVolumeLimit_zero (q : Set.Ioi (0 : ℝ)) (i : Fin 2) :
    ∃ μ, IsRCInfiniteVolumeLimit ⟨0, by norm_num⟩ q i μ :=
  ⟨Measure.dirac (fun _ => false), isRCInfiniteVolumeLimit_endpoint q i false⟩

/-- The frozen random-cluster infinite-volume measure exists at `p = 1`, for every `q > 0`. -/
theorem exists_isRCInfiniteVolumeLimit_one (q : Set.Ioi (0 : ℝ)) (i : Fin 2) :
    ∃ μ, IsRCInfiniteVolumeLimit ⟨1, by norm_num⟩ q i μ :=
  ⟨Measure.dirac (fun _ => true), isRCInfiniteVolumeLimit_endpoint q i true⟩

end PottsDiscontinuity.FK
