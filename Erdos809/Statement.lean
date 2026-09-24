import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Topology.Instances.Real.Lemmas
import Erdos809.RainbowCycles

/-!
# Erdős Problem 809: rainbow odd cycles

The final target quantifies over every odd cycle of length at least seven.
Its proof splits into the seven-cycle case and the longer-cycle
case. The exact-edge seven-cycle definitions below support the first branch.
The mathematical sources are listed in `formalization.yaml`; the proof of the
seven-cycle branch is developed in `Erdos809/SevenCycle/`.

We use simple graphs on `Fin n` and color only their edges. A seven-cycle is
specified by seven distinct vertices in cyclic order. The condition below
requires the colors of **every** such cycle to be pairwise distinct.

At the exact edge count `⌊n²/4⌋ + 1`, the problem asks for the asymptotic
minimum number of colors. Dividing by `n²` expresses the `o(n²)` term as a
limit.
-/

namespace Erdos809

/-- Every simple seven-cycle in `G` has seven distinct edge colors. -/
def EverySevenCycleRainbow {n k : ℕ} (G : SimpleGraph (Fin n))
    (C : G.EdgeLabeling (Fin k)) : Prop :=
  ∀ (v : Fin 7 → Fin n), Function.Injective v →
    ∀ (h : ∀ i : Fin 7, G.Adj (v i) (v (i + 1))),
      Function.Injective (fun i : Fin 7 => C.get (v i) (v (i + 1)) (h i))

/-- A graph at the prescribed edge count with a `k`-color labeling in which
every seven-cycle is rainbow. Natural-number division is the floor in
`⌊n²/4⌋ + 1`. -/
def Admissible (n k : ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (C : G.EdgeLabeling (Fin k)),
    Nat.card G.edgeSet = n * n / 4 + 1 ∧ EverySevenCycleRainbow G C

/-- The minimum admissible palette size. For the finitely many orders at
which the prescribed edge count is impossible, `sInf` returns zero; this has
no effect on the limit. -/
noncomputable def rainbowChromatic (n : ℕ) : ℕ :=
  sInf {k : ℕ | Admissible n k}

/-- The threshold conjecture for a fixed odd cycle of length 2k+1. -/
def ThresholdFor (k : ℕ) : Prop :=
  Filter.Tendsto
    (fun n : ℕ =>
      (maximalAntiRamsey n (n * n / 4 + 1)
        (SimpleGraph.cycleGraph (2 * k + 1)) : ℝ) /
        (n : ℝ) ^ 2)
    Filter.atTop (nhds ((1 : ℝ) / (8 : ℝ)))

/-- The full Burr-Erdős-Graham-Sós conjecture, for every k at least three. -/
def Statement : Prop :=
  ∀ k ≥ 3, ThresholdFor k

/-- The exact-edge rainbow-seven-cycle threshold is `n²/8 + o(n²)`. -/
def SevenCycleThreshold : Prop :=
  Filter.Tendsto
    (fun n : ℕ => (rainbowChromatic n : ℝ) / (n : ℝ) ^ 2)
    Filter.atTop (nhds ((1 : ℝ) / (8 : ℝ)))

end Erdos809
