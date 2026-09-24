import Erdos809.SevenCycle.Statement
import Erdos809.TwoCliqueCounts
import Erdos809.RainbowCyclesSum

/-!
# Rainbow seven-cycles in the two-clique construction
-/

namespace Erdos809

/-- Transfer the rainbow condition from the sum vertex set to its standard
`Fin (a + b)` numbering. -/
theorem twoCliqueRainbow_of_sum (m a b : ℕ)
    (hSum : EveryCycleRainbow (m + 1) (twoCliquesSum a b)
      (twoCliquesSumColoring a b)) :
    EveryCycleRainbow (m + 1) (twoCliqueGraph a b)
      (twoCliqueColoring a b) := by
  intro v hv h
  let w : Fin (m + 1) → Fin a ⊕ Fin b :=
    fun i => (twoCliqueGraphIso a b).symm (v i)
  have hw : Function.Injective w :=
    (twoCliqueGraphIso a b).symm.injective.comp hv
  have hEdges : ∀ i : Fin (m + 1), (twoCliquesSum a b).Adj (w i) (w (i + 1)) := by
    intro i
    exact (twoCliqueGraphIso a b).symm.map_rel_iff.mpr (h i)
  have hRainbow := hSum w hw hEdges
  have hcolor (i : Fin (m + 1)) :
      (twoCliqueColoring a b).get (v i) (v (i + 1)) (h i) =
        (twoCliquesSumColoring a b).get (w i) (w (i + 1)) (hEdges i) := by
    rfl
  simpa only [hcolor] using hRainbow

/-- The two-clique coloring makes every cycle of length at least three
rainbow. Each cycle lies in one clique, whose edges have distinct colors. -/
theorem twoCliqueRainbow_generic (m : ℕ) (hm : 2 ≤ m) (a b : ℕ) :
    EveryCycleRainbow (m + 1) (twoCliqueGraph a b)
      (twoCliqueColoring a b) := by
  apply twoCliqueRainbow_of_sum m a b
  exact everyCycleRainbow_sum hm (twoCliquesSumColoring a b)
      (twoCliquesSumColoring_left_injective a b)
      (twoCliquesSumColoring_right_injective a b)

/-- Specialization of the construction to seven-cycles. -/
theorem twoCliqueRainbow (a b : ℕ) :
    EverySevenCycleRainbow (twoCliqueGraph a b) (twoCliqueColoring a b) :=
  twoCliqueRainbow_generic 6 (by omega) a b

end Erdos809
