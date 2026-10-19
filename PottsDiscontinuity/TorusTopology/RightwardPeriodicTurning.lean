module

public import PottsDiscontinuity.TorusTopology.PeriodicSupportingLine
public import PottsDiscontinuity.TorusTopology.LatticeSequenceWalk
public import PottsDiscontinuity.TorusTopology.CompassWordBounds

/-! A simple periodic lattice curve with rightward deck displacement has zero
turn over a period. Thirty-two periods close by a return whose turn changes the
cyclic sum by at most eighteen; the planar Umlaufsatz then forces zero. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open SimpleGraph Finset Planar.Medial

/-- Discrete turning classification for an actual simple rightward-periodic curve. -/
theorem periodic_lattice_turn_eq_zero_of_pos_horizontal
    (f : ℕ → ℤ × ℤ) (hadj : ∀ n, FK.squareLattice.Adj (f n) (f (n+1)))
    (hf : Function.Injective f) (L : ℕ) (D : ℤ × ℤ) (hL : 0 < L)
    (hDx : 0 < D.1) (hper : ∀ n, f (n+L)=f n+D) :
    (∑ n ∈ range L, primalCompassQuarterTurn (sequenceCompass f hadj n)
      (sequenceCompass f hadj (n+1))) = 0 := by
  obtain ⟨k,hk,hmax⟩ := periodic_translation_supporting_phase f L D hL hper
  let g : ℕ → ℤ × ℤ := fun n => f (k+n)
  have hgadj : ∀ n, FK.squareLattice.Adj (g n) (g (n+1)) := by
    intro n; simpa [g,Nat.add_assoc] using hadj (k+n)
  have hginj : Function.Injective g := by
    intro a b he; have hh := hf he; omega
  have hgper : ∀ n, g (n+L)=g n+D := by
    intro n; simpa [g,Nat.add_assoc] using hper (k+n)
  let p := latticeSequenceWalk g hgadj (32*L)
  let u := g 0
  let v := g (32*L)
  have hend : v=u+32 • D := periodic_translation_mul g L D hgper 32
  have hxy : u.1 < v.1 := by
    rw [hend]
    change u.1 < u.1+(32 : ℕ) • D.1
    simp only [nsmul_eq_mul]
    omega
  have heq : deckNormalHeight D u = deckNormalHeight D v := by
    rw [hend,deckNormalHeight_add_deck]
  have hp := latticeSequenceWalk_isPath g hgadj hginj (32*L)
  have hbelow : ∀ z ∈ p.support, deckNormalHeight D z ≤ deckNormalHeight D u := by
    intro z hz
    rw [latticeSequenceWalk_support g hgadj (32*L)] at hz
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hz
    simpa [g,u] using hmax (k+n)
  let Y := max u.2 v.2+1
  have hu : u.2 < Y := by dsimp [Y]; have := le_max_left u.2 v.2; omega
  have hv : v.2 < Y := by dsimp [Y]; have := le_max_right u.2 v.2; omega
  have hlen : 1 < p.length := by simp only [p,latticeSequenceWalk_length]; omega
  let r := upperReturn u v Y hxy hu hv
  have hcycle := isCycle_append_upperReturn D u v hDx heq p hp hbelow Y hxy hu hv hlen
  have hturn := squareWalkCyclicTurn_eq_four_or_neg_four _ hcycle
  let a := sequenceCompass g hgadj
  let W := (List.range (32*L)).map a
  have hW : W ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [W,List.length_map,List.length_range,List.length_nil] at hh
    omega
  have hdirs : squareWalkCompassDirections (p.append r) =
      W++List.replicate (Y-v.2).toNat 1++List.replicate (v.1-u.1).toNat 2++
        List.replicate (Y-u.2).toNat 3 := by
    simp only [squareWalkCompassDirections,Walk.darts_append,List.map_append]
    change squareWalkCompassDirections p ++ squareWalkCompassDirections r = _
    rw [show squareWalkCompassDirections p = W from latticeSequenceWalk_compassDirections g hgadj (32*L),
      upperReturn_compassDirections u v Y hxy hu hv]
    simp only [List.append_assoc]
  have hbound := compassWordCyclicTurn_append_three_replicates_bound W hW 1 2 3
    (Y-v.2).toNat (v.1-u.1).toNat (Y-u.2).toNat (by omega) (by omega) (by omega)
  change compassWordCyclicTurn (squareWalkCompassDirections (p.append r)) = 4 ∨
    compassWordCyclicTurn (squareWalkCompassDirections (p.append r)) = -4 at hturn
  rw [hdirs] at hturn
  have hsmall : |compassWordCyclicTurn W| ≤ 22 := by
    rw [abs_le] at hbound ⊢
    rcases hturn with ht | ht <;> omega
  have ha : ∀ n, a (n+L)=a n := sequenceCompass_periodic g hgadj L D hgper
  let t : ℕ → ℤ := fun n => primalCompassQuarterTurn (a n) (a (n+1))
  have ht : ∀ n, t (n+L)=t n := by
    intro n; dsimp [t]; rw [ha,show n+L+1=n+1+L by omega,ha]
  have ha32 : a (32*L)=a 0 := by
    have hamul (r : ℕ) : a (r*L)=a 0 := by
      induction r with
      | zero => simp
      | succ r ih => rw [Nat.succ_mul,ha,ih]
    exact hamul 32
  have hsum : compassWordCyclicTurn W = 32 * ∑ n ∈ range L, t n := by
    rw [compassWordCyclicTurn_range a (32*L) (by omega) ha32]
    exact sum_periodic_mul t L ht 32
  rw [hsum,abs_le] at hsmall
  have hz : (∑ n ∈ range L, t n)=0 := by omega
  have htrans : ∀ n, t n = primalCompassQuarterTurn (sequenceCompass f hadj (k+n))
      (sequenceCompass f hadj (k+n+1)) := by
    intro n
    simp only [t,a,sequenceCompass,squareDartCompass,g,Nat.add_assoc]
  simp_rw [htrans] at hz
  have htf : ∀ n,
      primalCompassQuarterTurn (sequenceCompass f hadj (n+L))
        (sequenceCompass f hadj (n+L+1)) =
      primalCompassQuarterTurn (sequenceCompass f hadj n)
        (sequenceCompass f hadj (n+1)) := by
    intro n
    rw [sequenceCompass_periodic f hadj L D hper,
      show n+L+1=n+1+L by omega,sequenceCompass_periodic f hadj L D hper]
  have hshift := sum_periodic_shift
    (fun n => primalCompassQuarterTurn (sequenceCompass f hadj n)
      (sequenceCompass f hadj (n+1))) L htf k
  exact hshift.symm.trans hz

end PottsDiscontinuity.TorusTopology
