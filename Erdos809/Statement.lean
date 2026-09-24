import Mathlib.Topology.Instances.Real.Lemmas
import Erdos809.RainbowCycles

/-!
# Erdős Problem 809: rainbow odd cycles

The final target quantifies over every odd cycle of length at least seven.
The general maximal anti-Ramsey function uses copies of Mathlib's
`cycleGraph`, so cycles may have chords in the host graph.

The seven-cycle proof uses an exact-edge formulation in
`Erdos809/SevenCycle/Statement.lean`. `Erdos809/Comparison.lean` relates it
to the general function used here. The mathematical sources are listed in
`formalization.yaml`.
-/

namespace Erdos809

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

end Erdos809
