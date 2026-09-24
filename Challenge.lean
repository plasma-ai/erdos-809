import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Order.Lattice.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Erdős Problem 809: rainbow odd cycles

This is the statement surface for the published result. An edge coloring uses
at most `c` colors; every simple cycle of the specified length must have
pairwise distinct edge colors. Cycles are copies of `cycleGraph`, so chords in
the host graph are allowed. Among graphs on `n` vertices with at least
`⌊n²/4⌋ + 1` edges, the least possible palette size is asymptotic to `n²/8`
for every fixed odd cycle length at least seven.

The theorem below has a deliberate proof hole. `Solution.lean` supplies the
proof, and Comparator checks that it proves this exact statement.
-/

open scoped Asymptotics

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

/-- The threshold conjecture for a fixed odd cycle of length `2 * k + 1`. -/
def ThresholdFor (k : ℕ) : Prop :=
  (fun n : ℕ =>
    (maximalAntiRamsey n (n * n / 4 + 1)
      (SimpleGraph.cycleGraph (2 * k + 1)) : ℝ))
    ~[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ 2 / 8)

/-- The threshold claim for every odd cycle of length at least seven. -/
def Statement : Prop := ∀ k ≥ 3, ThresholdFor k

/-- The rainbow odd-cycle threshold at `⌊n²/4⌋ + 1` edges. -/
theorem main_result : Statement := by
  sorry

end Erdos809
