import Erdos809.SevenCycle.Statement
import Erdos809.SubgraphTransfer
import Erdos809.TwoCliqueRainbow
import Erdos809.TwoCliqueArithmetic

/-!
# The finite two-clique upper bound

The two-clique graph can be thinned to the exact edge target. Every seven-cycle
in it is rainbow because each cycle stays in one clique.
-/

namespace Erdos809

/-- Once the two-clique graph has enough edges, its larger component's edge
count bounds the minimum palette size at the exact target. -/
theorem rainbowChromatic_le_twoCliquePalette (a b : ℕ)
    (hm : (a + b) * (a + b) / 4 + 1 ≤ a.choose 2 + b.choose 2) :
    rainbowChromatic (a + b) ≤ max (a.choose 2) (b.choose 2) := by
  have hEdges : (a + b) * (a + b) / 4 + 1 ≤
      Nat.card (twoCliqueGraph a b).edgeSet := by
    rw [twoCliqueGraph_edge_count]
    exact hm
  obtain ⟨H, _, hHedges, D, hD⟩ :=
    rainbow_subgraph_exact_edges (twoCliqueGraph a b) (twoCliqueColoring a b)
      (twoCliqueRainbow a b) hEdges
  apply Nat.sInf_le
  exact ⟨H, D, hHedges, hD⟩

/-- An explicit upper-bound construction at every order `n ≥ 16`. -/
theorem rainbowChromatic_le_chosenTwoCliquePalette (n : ℕ) (hn : 16 ≤ n) :
    rainbowChromatic n ≤
      max ((twoCliqueLargeSize n).choose 2) ((twoCliqueSmallSize n).choose 2) := by
  have h := rainbowChromatic_le_twoCliquePalette
    (twoCliqueLargeSize n) (twoCliqueSmallSize n) (by
      simpa only [twoCliqueSizes_add n hn] using twoClique_edge_surplus n hn)
  simpa only [twoCliqueSizes_add n hn] using h

/-- The construction proves the asymptotic upper half of the seven-cycle
threshold: for every positive error, the normalized minimum is eventually at
most `1/8` plus that error. -/
theorem rainbowChromatic_upper_asymptotic :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop,
        (rainbowChromatic n : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 8 + ε := by
  intro ε hε
  have herror : ∀ᶠ n : ℕ in Filter.atTop,
      ((Nat.sqrt n + 2 : ℕ) : ℝ) / (n : ℝ) < ε :=
    twoClique_error_tendsto_zero.eventually (eventually_lt_nhds hε)
  filter_upwards [herror, Filter.eventually_ge_atTop 16] with n herror_n hn
  have hcolor : (rainbowChromatic n : ℝ) ≤
      (max ((twoCliqueLargeSize n).choose 2)
        ((twoCliqueSmallSize n).choose 2) : ℝ) := by
    exact_mod_cast rainbowChromatic_le_chosenTwoCliquePalette n hn
  calc
    (rainbowChromatic n : ℝ) / (n : ℝ) ^ 2 ≤
        (max ((twoCliqueLargeSize n).choose 2)
          ((twoCliqueSmallSize n).choose 2) : ℝ) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hcolor (sq_nonneg _)
    _ ≤ 1 / 8 + ((Nat.sqrt n : ℝ) + 2) / n :=
      twoClique_palette_ratio_bound n hn
    _ ≤ 1 / 8 + ε := by
      have herror_n' : ((Nat.sqrt n : ℝ) + 2) / n < ε := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using herror_n
      linarith

end Erdos809
