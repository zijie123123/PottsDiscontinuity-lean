module

public import Mathlib

/-!
# The six-vertex model on the torus and its transfer matrix: definitions

Sources: arXiv:1611.09877v2, (1.4) (`eq:w_6V`), (1.5) (`eq:V`) and §3.3 (definition of `|ω|`,
`Z_6V(N,M)` and `Z^{(r)}_{6V}(N,M)`); companion paper arXiv:1611.09909v1, §2.1 and §4.

## Conventions

* The torus `T_{N,M} = ℤ/N × ℤ/M` is `Fin N × Fin M`; the cyclic successor / predecessor on `Fin n`
  are `nxt = finRotate n` and `prv = (finRotate n).symm` (so `nxt i = i + 1 mod n`).  Every edge of the
  torus is indexed by its left (resp. lower) endpoint: `horiz (i, j)` is the edge from `(i, j)` to
  `(i + 1, j)` and `vert (i, j)` the edge from `(i, j)` to `(i, j + 1)`.  This gives the `2NM` edges
  of the torus (a multigraph if `N ≤ 2` or `M ≤ 2`, with loops if `N = 1` or `M = 1`; this is the
  reading under which the number of arrow configurations is `4^{NM}` as stated in the companion
  paper, and under which the trace formula holds for all `N, M ≥ 1`).
* An arrow configuration `ω` is a pair of Boolean fields: `horiz v = true` means the arrow of the edge
  from `v` to `v + (1,0)` points right (towards `v + (1,0)`), `vert v = true` means that the arrow of
  the edge from `v` to `v + (0,1)` points up (towards `v + (0,1)`).
* The ice rule: every vertex has exactly two incident edges pointing towards it.
* The six vertex types are indexed `t1, …, t6` as in the figure of the papers: `t1, t2` (weight `a`)
  are the vertices whose horizontal and vertical arrows all point right/up (resp. left/down), `t3, t4`
  (weight `b`) the two remaining "straight-through" vertices, `t5, t6` (weight `c`) the sources and
  sinks of the vertical arrows (the two vertical arrows both enter, resp. both leave the vertex; the
  two horizontal arrows then both leave, resp. enter it).  The companion paper §4 uses exactly that
  `t5, t6` are "sources and sinks"; since only `a = b = 1` is used below, the numbering inside the
  pairs `{t1,t2}` and `{t3,t4}` is immaterial.
* `|ω|` is the number of up arrows on the vertical edges leaving row `0`; by the ice rule it is the
  same on every row (`SixVertex.rowUp_eq_absUp` in `TraceFormula`).
* States `Ψ_x` of the transfer matrix are indexed by `x : Finset (Fin N)` (positions of up arrows);
  `Fin N = {0, …, N-1}` replaces `{1, …, N}` (same order).
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

/-! ### The torus and arrow configurations -/

/-- Cyclic successor on `Fin n` (`i + 1 mod n`). -/
abbrev nxt {n : ℕ} (i : Fin n) : Fin n := finRotate n i

/-- Cyclic predecessor on `Fin n` (`i - 1 mod n`). -/
abbrev prv {n : ℕ} (i : Fin n) : Fin n := (finRotate n).symm i

/-- An arrow configuration on the torus `ℤ/N × ℤ/M`: one orientation per edge.
`horiz v = true` iff the edge `{v, v + (1,0)}` points right; `vert v = true` iff the edge
`{v, v + (0,1)}` points up. -/
@[ext]
structure ArrowConfig (N M : ℕ) where
  horiz : Fin N × Fin M → Bool
  vert : Fin N × Fin M → Bool

/-- Arrow configurations are in bijection with pairs of Boolean fields on the vertices. -/
def ArrowConfig.equivProd (N M : ℕ) :
    ArrowConfig N M ≃ (Fin N × Fin M → Bool) × (Fin N × Fin M → Bool) where
  toFun ω := (ω.horiz, ω.vert)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (N M : ℕ) : Fintype (ArrowConfig N M) :=
  Fintype.ofEquiv _ (ArrowConfig.equivProd N M).symm

instance (N M : ℕ) : DecidableEq (ArrowConfig N M) := fun ω ω' =>
  decidable_of_iff (ω.horiz = ω'.horiz ∧ ω.vert = ω'.vert)
    ⟨fun h => ArrowConfig.ext h.1 h.2, fun h => h ▸ ⟨rfl, rfl⟩⟩

variable {N M : ℕ}

namespace ArrowConfig

/-- The edge to the left of `v` (from `v - (1,0)` to `v`); `true` iff it points towards `v`. -/
def left (ω : ArrowConfig N M) (v : Fin N × Fin M) : Bool := ω.horiz (prv v.1, v.2)

/-- The edge to the right of `v` (from `v` to `v + (1,0)`); `true` iff it points away from `v`. -/
def right (ω : ArrowConfig N M) (v : Fin N × Fin M) : Bool := ω.horiz v

/-- The edge below `v` (from `v - (0,1)` to `v`); `true` iff it points towards `v` (up arrow). -/
def below (ω : ArrowConfig N M) (v : Fin N × Fin M) : Bool := ω.vert (v.1, prv v.2)

/-- The edge above `v` (from `v` to `v + (0,1)`); `true` iff it points away from `v` (up arrow). -/
def above (ω : ArrowConfig N M) (v : Fin N × Fin M) : Bool := ω.vert v

end ArrowConfig

/-! ### Ice rule and vertex types -/

/-- Number of the four edges at a vertex that point towards it, in terms of the four arrows
`l` (left edge, `true` = pointing right), `r` (right edge, `true` = pointing right),
`d` (lower edge, `true` = pointing up), `u` (upper edge, `true` = pointing up). -/
def inDegree (l r d u : Bool) : ℕ :=
  (if l then 1 else 0) + (if r then 0 else 1) + (if d then 1 else 0) + (if u then 0 else 1)

/-- The ice rule: every vertex of the torus has exactly two incident edges pointing towards it. -/
def ArrowConfig.IceRule (ω : ArrowConfig N M) : Prop :=
  ∀ v : Fin N × Fin M, inDegree (ω.left v) (ω.right v) (ω.below v) (ω.above v) = 2

instance (ω : ArrowConfig N M) : Decidable ω.IceRule := by
  unfold ArrowConfig.IceRule; infer_instance

/-- The six vertex configurations allowed by the ice rule. -/
inductive VertexType
  | t1 | t2 | t3 | t4 | t5 | t6
  deriving DecidableEq

/-- The type `1, …, 6` of the vertex whose left, right, lower, upper arrows are `l, r, d, u`
(`none` if the vertex violates the ice rule). -/
def vertexType? : Bool → Bool → Bool → Bool → Option VertexType
  | true, true, true, true => some .t1
  | false, false, false, false => some .t2
  | true, true, false, false => some .t3
  | false, false, true, true => some .t4
  | true, false, false, true => some .t5
  | false, true, true, false => some .t6
  | _, _, _, _ => none

/-- The weight `a`, `b` or `c` of a vertex type (`a` for types 1, 2; `b` for 3, 4; `c` for 5, 6). -/
def vertexWeight (a b c : ℝ) : VertexType → ℝ
  | .t1 => a | .t2 => a | .t3 => b | .t4 => b | .t5 => c | .t6 => c

/-- `n_t(ω)`: the number of vertices of type `t` in `ω`. -/
def ArrowConfig.numType (ω : ArrowConfig N M) (t : VertexType) : ℕ :=
  (univ.filter fun v => vertexType? (ω.left v) (ω.right v) (ω.below v) (ω.above v) = some t).card

/-- The weight (1.4): `w(ω) = a^{n₁+n₂} b^{n₃+n₄} c^{n₅+n₆}` if `ω` satisfies the ice rule and
`0` otherwise. -/
def w6V (a b c : ℝ) (ω : ArrowConfig N M) : ℝ :=
  if ω.IceRule then
    a ^ (ω.numType .t1 + ω.numType .t2) * b ^ (ω.numType .t3 + ω.numType .t4) *
      c ^ (ω.numType .t5 + ω.numType .t6)
  else 0

/-- The weight with `a = b = 1` and `c` arbitrary (the case used throughout the paper). -/
def w6V1 (c : ℝ) (ω : ArrowConfig N M) : ℝ := w6V 1 1 c ω

/-! ### The row statistic and the partition functions -/

/-- The number of up arrows among the vertical edges leaving row `j`. -/
def ArrowConfig.rowUp (ω : ArrowConfig N M) (j : Fin M) : ℕ :=
  (univ.filter fun i : Fin N => ω.vert (i, j) = true).card

/-- `|ω|`: the number of up arrows on each row (the value on row `0`; it is the same on every row
for configurations satisfying the ice rule, see `rowUp_eq_absUp`). -/
def ArrowConfig.absUp (ω : ArrowConfig N M) : ℕ :=
  if h : 0 < M then ω.rowUp ⟨0, h⟩ else 0

/-- `Z_6V(N, M) = ∑_ω w(ω)` over all arrow configurations of the torus `T_{N,M}` (weights
`a = b = 1`, `c`). -/
def Z6V (c : ℝ) (N M : ℕ) : ℝ := ∑ ω : ArrowConfig N M, w6V1 c ω

/-- The part of `Z_6V(N,M)` with `n` up arrows per row: `∑_{ω : |ω| = n} w(ω)`. -/
def Z6Vn (c : ℝ) (N M n : ℕ) : ℝ := ∑ ω : ArrowConfig N M with ω.absUp = n, w6V1 c ω

/-- `Z^{(r)}_{6V}(N, M) = ∑_{ω : |ω| = N/2 - r} w(ω)`, written as `|ω| + r = N / 2` so that no
truncated subtraction occurs (`N` even in the source; for `r > N/2` the sum is empty). -/
def Z6Vr (c : ℝ) (N M r : ℕ) : ℝ := ∑ ω : ArrowConfig N M with ω.absUp + r = N / 2, w6V1 c ω

/-! ### The transfer matrix (1.5) -/

/-- The state `Ψ_x ∈ {±1}^N`: `+1` at the positions of `x` and `-1` elsewhere. -/
def Psi (x : Finset (Fin N)) (i : Fin N) : ℤ := if i ∈ x then 1 else -1

/-- `x_1 ≤ y_1 ≤ x_2 ≤ ⋯ ≤ x_n ≤ y_n` for the increasing enumerations of `x` and `y`
(this includes `|x| = |y| = n`). -/
def InterlacedLE (x y : Finset (Fin N)) : Prop :=
  ∃ h : x.card = y.card,
    (∀ k : Fin x.card, x.orderEmbOfFin rfl k ≤ y.orderEmbOfFin h.symm k) ∧
    ∀ k l : Fin x.card, k.val + 1 = l.val → y.orderEmbOfFin h.symm k ≤ x.orderEmbOfFin rfl l

/-- `x` and `y` are interlaced: `|x| = |y| = n` and `x_1 ≤ y_1 ≤ x_2 ≤ ⋯ ≤ x_n ≤ y_n` or
`y_1 ≤ x_1 ≤ y_2 ≤ ⋯ ≤ y_n ≤ x_n`. -/
def Interlaced (x y : Finset (Fin N)) : Prop := InterlacedLE x y ∨ InterlacedLE y x

open Classical in
noncomputable instance (x y : Finset (Fin N)) : Decidable (Interlaced x y) :=
  Classical.propDecidable _

/-- The transfer matrix `V = V(N, c)` of (1.5), indexed by the basis vectors `Ψ_x`,
`x ⊆ {0, …, N-1}`: `V(x,x) = 2`; `V(x,y) = c^{|{i : Ψ_x(i) ≠ Ψ_y(i)}|}` if `x ≠ y` are interlaced;
`0` otherwise. -/
noncomputable def transferMatrix (N : ℕ) (c : ℝ) :
    Matrix (Finset (Fin N)) (Finset (Fin N)) ℝ :=
  fun x y =>
    if x = y then 2
    else if Interlaced x y then c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card
    else 0

/-- The index set of the block `V^{[n]}`: the basis vectors `Ψ_x` with `x` having `n` entries. -/
abbrev State (N n : ℕ) : Type := {x : Finset (Fin N) // x.card = n}

/-- The block `V^{[n]}` of the transfer matrix: the action of `V` on `Ω_n = Vect(Ψ_x : |x| = n)`. -/
noncomputable def transferBlock (N : ℕ) (c : ℝ) (n : ℕ) : Matrix (State N n) (State N n) ℝ :=
  (transferMatrix N c).submatrix Subtype.val Subtype.val

end PottsDiscontinuity.SixVertex
