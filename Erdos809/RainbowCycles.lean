import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Order.Lattice.Nat
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Rainbow copies and the maximal anti-Ramsey function

An edge labeling with `Fin colors` is a coloring using at most `colors` colors.
The general function minimizes this palette size over graphs with **at least**
the specified number of edges, as in the maximal anti-Ramsey definition of
Bucić, Chen, and Ma. The indexed-cycle formulation below is used in the proofs.
-/

namespace Erdos809

/-- Every copy of `H` in `G` has pairwise distinct edge colors. -/
def EveryCopyRainbow {U V : Type*} {c : ℕ}
    (H : SimpleGraph U) (G : SimpleGraph V)
    (C : G.EdgeLabeling (Fin c)) : Prop :=
  ∀ f : H.Copy G,
    Function.Injective (fun e : H.edgeSet => C (f.mapEdgeSet e))

/-- An `n`-vertex graph with at least `e` edges in which every copy of `H`
is rainbow under a palette of `c` colors. -/
def AdmissibleAtLeast (n e c : ℕ) {U : Type*} (H : SimpleGraph U) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (C : G.EdgeLabeling (Fin c)),
    e ≤ Nat.card G.edgeSet ∧ EveryCopyRainbow H G C

/-- The least admissible palette size for the pattern graph `H`. If the edge
requirement is impossible, the admissible set is empty and `sInf` is zero. -/
noncomputable def maximalAntiRamsey (n e : ℕ) {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {c : ℕ | AdmissibleAtLeast n e c H}

/-- Every cycle of length `length` in `G` has pairwise distinct edge colors.
The applications below have `length ≥ 3`. -/
def EveryCycleRainbow {V : Type*} {colors : ℕ} (length : ℕ) [NeZero length]
    (G : SimpleGraph V) (C : G.EdgeLabeling (Fin colors)) : Prop :=
  ∀ (v : Fin length → V), Function.Injective v →
    ∀ (h : ∀ i : Fin length, G.Adj (v i) (v (i + 1))),
      Function.Injective (fun i : Fin length => C.get (v i) (v (i + 1)) (h i))

/-- The undirected edges of a simple cycle of length at least three are
distinct. -/
theorem cycleEdges_injective {V : Type*} {length : ℕ} [NeZero length]
    (hlength : 3 ≤ length) (v : Fin length → V) (hv : Function.Injective v) :
    Function.Injective (fun i : Fin length => s(v i, v (i + 1))) := by
  intro i j hij
  change s(v i, v (i + 1)) = s(v j, v (j + 1)) at hij
  rcases Sym2.eq_iff.mp hij with h | h
  · exact hv h.1
  · have hi : i = j + 1 := hv h.1
    have hj : i + 1 = j := hv h.2
    have htwo : i + 1 + 1 = i := by rw [hj, ← hi]
    have h11 : (1 + 1 : Fin length) = 0 := by
      have htwo' : i + (1 + 1 : Fin length) = i + 0 := by
        simpa only [add_assoc, add_zero] using htwo
      exact add_left_cancel htwo'
    have hval := congrArg Fin.val h11
    simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < length by omega),
      Nat.mod_eq_of_lt (show 2 < length by omega)] at hval

/-- An `n`-vertex graph with at least `edges` edges whose cycles of the
specified length are all rainbow under a palette of `colors` colors. -/
def AdmissibleCycleAtLeast (n edges length colors : ℕ) [NeZero length] : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (C : G.EdgeLabeling (Fin colors)),
    edges ≤ Nat.card G.edgeSet ∧ EveryCycleRainbow length G C

/-- The minimum palette size in the maximal anti-Ramsey problem for cycles.
If the edge requirement is impossible, the admissible set is empty and `sInf`
is zero; all asymptotic statements below stay in the feasible range. -/
noncomputable def maximalAntiRamseyCycle (n edges length : ℕ) [NeZero length] : ℕ :=
  sInf {colors : ℕ | AdmissibleCycleAtLeast n edges length colors}

end Erdos809
