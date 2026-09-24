import Erdos809.SevenCycle.Statement
import Erdos809.SevenCycle.UpperBound
import Mathlib.Topology.Order.Basic

/-!
# Closing the seven-cycle asymptotic argument

The two-clique construction ensures that the exact-edge optimization problem is
nonempty for every order at least sixteen, so its natural-number infimum is
attained. Any eventual lower palette bound for all admissible colorings then
combines with the proved upper bound to give the seven-cycle threshold.
-/

namespace Erdos809

/-- An exact-edge rainbow-colored graph exists at every order `n ≥ 16`. -/
theorem exists_admissible_of_sixteen_le (n : ℕ) (hn : 16 ≤ n) :
    ∃ k : ℕ, Admissible n k := by
  let a := twoCliqueLargeSize n
  let b := twoCliqueSmallSize n
  have hab : a + b = n := twoCliqueSizes_add n hn
  have hEnough : (a + b) * (a + b) / 4 + 1 ≤
      Nat.card (twoCliqueGraph a b).edgeSet := by
    rw [twoCliqueGraph_edge_count]
    simpa only [hab] using twoClique_edge_surplus n hn
  obtain ⟨H, _, hEdges, C, hRainbow⟩ :=
    rainbow_subgraph_exact_edges (twoCliqueGraph a b)
      (twoCliqueColoring a b) (twoCliqueRainbow a b) hEnough
  have hAdmissible : Admissible (a + b) (max (a.choose 2) (b.choose 2)) :=
    ⟨H, C, hEdges, hRainbow⟩
  exact ⟨max (a.choose 2) (b.choose 2), hab ▸ hAdmissible⟩

/-- The minimum palette size is achieved by an exact-edge rainbow coloring
at every order `n ≥ 16`. -/
theorem rainbowChromatic_admissible_of_sixteen_le (n : ℕ) (hn : 16 ≤ n) :
    Admissible n (rainbowChromatic n) := by
  rcases exists_admissible_of_sixteen_le n hn with ⟨k, hk⟩
  unfold rainbowChromatic
  have hs : ({j : ℕ | Admissible n j} : Set ℕ).Nonempty := ⟨k, hk⟩
  exact Nat.sInf_mem hs

/-- A lower bound for every admissible palette applies to the actual
minimum once the finite optimization problem is nonempty. -/
theorem rainbowChromatic_lower_of_admissible (n : ℕ) (hn : 16 ≤ n)
    (L : ℝ) (hL : ∀ k : ℕ, Admissible n k → L ≤ (k : ℝ)) :
    L ≤ (rainbowChromatic n : ℝ) :=
  hL _ (rainbowChromatic_admissible_of_sixteen_le n hn)

/-- The upper construction and an eventual universal lower bound imply
the seven-cycle threshold. The lower bound is stated on admissible palettes,
which directly represent exact-edge rainbow colorings. -/
theorem sevenCycleThreshold_of_eventual_palette_lower
    (hLower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ k : ℕ, Admissible n k →
          (1 / 8 - ε) * (n : ℝ) ^ 2 ≤ (k : ℝ)) :
    SevenCycleThreshold := by
  unfold SevenCycleThreshold
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let ε : ℝ := (1 / 8 - a) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [hLower ε hε, Filter.eventually_ge_atTop 16] with n hnLower hn
    have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := by
      have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity
    have hGap : a < 1 / 8 - ε := by dsimp [ε]; linarith
    have hBound : (1 / 8 - ε) * (n : ℝ) ^ 2 ≤
        (rainbowChromatic n : ℝ) :=
      hnLower _ (rainbowChromatic_admissible_of_sixteen_le n hn)
    exact (lt_div_iff₀ hnSq).mpr <|
      (mul_lt_mul_of_pos_right hGap hnSq).trans_le hBound
  · intro a ha
    let ε : ℝ := (a - 1 / 8) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [rainbowChromatic_upper_asymptotic ε hε] with n hnUpper
    have hGap : 1 / 8 + ε < a := by dsimp [ε]; linarith
    exact hnUpper.trans_lt hGap

/-- The same closure theorem with the lower bound phrased directly for
every exact-edge rainbow graph and edge coloring. -/
theorem sevenCycleThreshold_of_eventual_graph_lower
    (hLower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (k : ℕ) (G : SimpleGraph (Fin n)) (C : G.EdgeLabeling (Fin k)),
          Nat.card G.edgeSet = n * n / 4 + 1 →
          EverySevenCycleRainbow G C →
          (1 / 8 - ε) * (n : ℝ) ^ 2 ≤ (k : ℝ)) :
    SevenCycleThreshold := by
  apply sevenCycleThreshold_of_eventual_palette_lower
  intro ε hε
  filter_upwards [hLower ε hε] with n hn k hk
  rcases hk with ⟨G, C, hEdges, hRainbow⟩
  exact hn k G C hEdges hRainbow

end Erdos809
