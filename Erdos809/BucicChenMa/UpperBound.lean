import Erdos809.BucicChenMa.Statement
import Erdos809.BucicChenMa.UpperConstruction
import Erdos809.BucicChenMa.UpperError
import Erdos809.BucicChenMa.UpperArithmetic

/-!
# The upper half of the Bucić–Chen–Ma asymptotic formula

The graph construction and the finite palette estimate are kept separate:
the first uses the rainbow property of cycles in disjoint cliques, while the
second estimates the chosen clique sizes.
-/

namespace Erdos809.BucicChenMa

/-- An edge-rich two-clique graph with a palette estimate bounds the maximal
anti-Ramsey function at the same order and edge threshold. -/
theorem upperBound_of_twoCliqueEstimates (k n e a b : ℕ) (hk : 4 ≤ k)
    (hab : a + b = n) (he : e ≤ a.choose 2 + b.choose 2)
    (hp : (max (a.choose 2) (b.choose 2) : ℝ) ≤
      mainTerm n e + 3 * (n : ℝ) * ((Nat.sqrt n : ℝ) + 2))
    (ε : ℝ) (hs : 3 * (n : ℝ) * ((Nat.sqrt n : ℝ) + 2) ≤ ε * (n : ℝ) ^ 2) :
    (maximalAntiRamseyCycle n e (2 * k + 1) : ℝ) ≤
      mainTerm n e + ε * (n : ℝ) ^ 2 := by
  have hPalette := maximalAntiRamseyCycle_le_twoCliquePalette k a b e (by omega) he
  rw [hab] at hPalette
  have hPaletteR : (maximalAntiRamseyCycle n e (2 * k + 1) : ℝ) ≤
      (max (a.choose 2) (b.choose 2) : ℝ) := by exact_mod_cast hPalette
  linarith

/-- The upper half of Theorem 1.2, with error uniform across the entire
nontrivial edge-density range. -/
def UpperDensityFormula (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ e : ℕ, n * n / 4 + 1 ≤ e → e ≤ n.choose 2 →
        (maximalAntiRamseyCycle n e (2 * k + 1) : ℝ) ≤
          mainTerm n e + ε * (n : ℝ) ^ 2

/-- The two-clique construction proves the full-density upper asymptotic
for each fixed `k ≥ 4`. -/
theorem upperDensityFormula (k : ℕ) (hk : 4 ≤ k) : UpperDensityFormula k := by
  intro ε hε
  obtain ⟨N, hN⟩ := upperError_eventually_small ε hε
  refine ⟨max 16 N, ?_⟩
  intro n hn e hlo hhi
  exact upperBound_of_twoCliqueEstimates k n e (largeSize n e) (smallSize n e) hk
    (sizes_add n e) (edge_capacity n e hlo hhi)
    (palette_bound n e (by omega) hlo hhi) ε (hN n (by omega))

/-- The upper asymptotic for every cycle length in the Bucić–Chen–Ma
range. -/
def UpperStatement : Prop :=
  ∀ k : ℕ, 4 ≤ k → UpperDensityFormula k

theorem upperStatement : UpperStatement := by
  intro k hk
  exact upperDensityFormula k hk

end Erdos809.BucicChenMa
