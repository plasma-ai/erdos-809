import Erdos809.Statement
import Erdos809.SevenCycle.C7LowerSequence
import Erdos809.Comparison
import Erdos809.CycleCopyBridge
import Erdos809.BucicChenMa.ThresholdConsequence
import Erdos809.BucicChenMa.QuantitativeInductionAssembly

/-!
# Assembling the full odd-cycle threshold statement

The final Erdős 809 statement covers every k at least three. The seven-cycle
branch is proved in `C7LowerSequence`; the longer-cycle branch is the
Bucić–Chen–Ma full-density theorem.
-/

namespace Erdos809

/-- The general graph-copy threshold agrees with the indexed-cycle threshold
used in the longer-cycle proof. -/
private theorem thresholdFor_iff_cycleThresholdFormula (k : ℕ) (hk : 3 ≤ k) :
    ThresholdFor k ↔ BucicChenMa.ThresholdFormula k := by
  unfold ThresholdFor BucicChenMa.ThresholdFormula
  have hm : 3 ≤ 2 * k + 1 := by omega
  simp only [maximalAntiRamsey_cycleGraph hm]

/-- The exact-edge seven-cycle result and the longer-cycle thresholds imply
the full conjecture. -/
theorem statement_of_sevenCycle_and_higherThreshold
    (h7 : SevenCycleThreshold)
    (hHigher : BucicChenMa.ThresholdStatement) : Statement := by
  intro k hk
  by_cases hthree : k = 3
  · subst k
    apply (thresholdFor_iff_cycleThresholdFormula 3 (by omega)).mpr
    simpa [BucicChenMa.ThresholdFormula, SevenCycleThreshold,
      rainbowChromatic_eq_maximalAntiRamseyCycle] using h7
  · have hfour : 4 ≤ k := by omega
    exact (thresholdFor_iff_cycleThresholdFormula k hk).mpr (hHigher k hfour)

/-- The Bucić–Chen–Ma full-density result supplies the longer-cycle branch. -/
theorem statement_of_sevenCycle_and_higherDensity
    (h7 : SevenCycleThreshold)
    (hHigher : BucicChenMa.Statement) : Statement :=
  statement_of_sevenCycle_and_higherThreshold h7
    (BucicChenMa.statement_implies_threshold hHigher)

/-- The proved seven-cycle branch reduces the full statement to the
Bucić–Chen–Ma higher-cycle theorem. -/
theorem statement_of_higherDensity
    (hHigher : BucicChenMa.Statement) : Statement :=
  statement_of_sevenCycle_and_higherDensity sevenCycleThreshold_proved hHigher

/-- The full rainbow odd-cycle threshold theorem for every `k ≥ 3`. -/
theorem statement_proved : Statement :=
  statement_of_higherDensity BucicChenMa.statement_proved

end Erdos809
