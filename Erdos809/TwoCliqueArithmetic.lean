import Erdos809.SevenCycle.Statement
import Erdos809.TwoCliqueCounts
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The sizes of the two cliques

The larger clique differs from half the order by only `√n + 2`.  The
following estimates put its total edge count above the Turán threshold and
bound the number of colors used by the construction.
-/

namespace Erdos809

/-- The size of the larger clique in the upper-bound construction. -/
def twoCliqueLargeSize (n : ℕ) : ℕ := n / 2 + Nat.sqrt n + 2

/-- The size of the smaller clique in the upper-bound construction. -/
def twoCliqueSmallSize (n : ℕ) : ℕ := n - twoCliqueLargeSize n

private theorem sqrt_bounds (n : ℕ) (hn : 16 ≤ n) :
    4 ≤ Nat.sqrt n ∧ (Nat.sqrt n) ^ 2 ≤ n ∧ n < (Nat.sqrt n + 1) ^ 2 := by
  refine ⟨?_, Nat.sqrt_le' n, ?_⟩
  · exact Nat.le_sqrt'.2 (by nlinarith)
  · simpa [pow_two] using Nat.lt_succ_sqrt n

private theorem offset_fits (n : ℕ) (hn : 16 ≤ n) :
    Nat.sqrt n + 2 ≤ n / 2 := by
  obtain ⟨hs, hslo, _⟩ := sqrt_bounds n hn
  have hdiv : n % 2 < 2 := Nat.mod_lt _ (by omega)
  have hdecomp : n % 2 + 2 * (n / 2) = n := Nat.mod_add_div n 2
  nlinarith [sq_nonneg ((Nat.sqrt n : ℤ) - 4)]

theorem twoCliqueLargeSize_le (n : ℕ) (hn : 16 ≤ n) :
    twoCliqueLargeSize n ≤ n := by
  unfold twoCliqueLargeSize
  have h := offset_fits n hn
  omega

theorem twoCliqueSizes_add (n : ℕ) (hn : 16 ≤ n) :
    twoCliqueLargeSize n + twoCliqueSmallSize n = n := by
  unfold twoCliqueSmallSize
  exact Nat.add_sub_of_le (twoCliqueLargeSize_le n hn)

private theorem choose_two_cast (k : ℕ) :
    (k.choose 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  exact Nat.cast_choose_two ℝ k

private theorem twoClique_edge_surplus_real (n : ℕ) (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 / 4 + 1 ≤
      (twoCliqueLargeSize n |>.choose 2 : ℝ) +
        (twoCliqueSmallSize n |>.choose 2 : ℝ) := by
  let a := twoCliqueLargeSize n
  let b := twoCliqueSmallSize n
  let s := Nat.sqrt n
  let m := n / 2
  have hab : (a : ℝ) + (b : ℝ) = n := by
    exact_mod_cast twoCliqueSizes_add n hn
  have ha : (a : ℝ) = (m : ℝ) + (s : ℝ) + 2 := by
    simp [a, m, s, twoCliqueLargeSize]
  have hfloor_nat : n ≤ 2 * m + 1 := by
    have := Nat.mod_add_div n 2
    have := Nat.mod_lt n (by omega : 0 < 2)
    omega
  have hfloor : (n : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hfloor_nat
  have hsupper_nat := (sqrt_bounds n hn).2.2
  have hsupper : (n : ℝ) < ((s : ℝ) + 1) ^ 2 := by
    exact_mod_cast hsupper_nat
  have hsnon : (0 : ℝ) ≤ s := by positivity
  have hdiff : 0 ≤ (a : ℝ) - b - (2 * (s : ℝ) + 3) := by
    linarith
  have hsum : 0 ≤ (a : ℝ) - b + (2 * (s : ℝ) + 3) := by
    linarith
  have hsquare : (2 * (s : ℝ) + 3) ^ 2 ≤ ((a : ℝ) - b) ^ 2 := by
    nlinarith [mul_nonneg hdiff hsum]
  rw [choose_two_cast, choose_two_cast]
  nlinarith [sq_nonneg (s : ℝ)]

/-- The two cliques contain at least one edge above the balanced complete
bipartite graph's edge count. -/
theorem twoClique_edge_surplus (n : ℕ) (hn : 16 ≤ n) :
    n * n / 4 + 1 ≤
      (twoCliqueLargeSize n).choose 2 + (twoCliqueSmallSize n).choose 2 := by
  have hreal := twoClique_edge_surplus_real n hn
  have hdiv : ((n * n / 4 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by
    simpa [pow_two] using (Nat.cast_div_le (m := n * n) (n := 4) (α := ℝ))
  have hnat : ((n * n / 4 + 1 : ℕ) : ℝ) ≤
      ((twoCliqueLargeSize n).choose 2 + (twoCliqueSmallSize n).choose 2 : ℕ) := by
    push_cast
    linarith
  exact_mod_cast hnat

theorem twoCliqueSmallSize_le_largeSize (n : ℕ) (hn : 16 ≤ n) :
    twoCliqueSmallSize n ≤ twoCliqueLargeSize n := by
  have hadd := twoCliqueSizes_add n hn
  have hfloor : n ≤ 2 * (n / 2) + 1 := by
    have := Nat.mod_add_div n 2
    have := Nat.mod_lt n (by omega : 0 < 2)
    omega
  unfold twoCliqueLargeSize twoCliqueSmallSize at *
  omega

/-- The reused palette has at most `n²/8 + n(√n + 2)` colors. -/
theorem twoClique_palette_bound (n : ℕ) (hn : 16 ≤ n) :
    (max ((twoCliqueLargeSize n).choose 2) ((twoCliqueSmallSize n).choose 2) : ℝ) ≤
      (n : ℝ) ^ 2 / 8 + n * ((Nat.sqrt n : ℝ) + 2) := by
  let a := twoCliqueLargeSize n
  let b := twoCliqueSmallSize n
  let s := Nat.sqrt n
  let m := n / 2
  have hba : b ≤ a := twoCliqueSmallSize_le_largeSize n hn
  have hchoose : b.choose 2 ≤ a.choose 2 := Nat.choose_le_choose 2 hba
  change max (a.choose 2 : ℝ) (b.choose 2 : ℝ) ≤
    (n : ℝ) ^ 2 / 8 + n * ((s : ℝ) + 2)
  rw [max_eq_left (show (b.choose 2 : ℝ) ≤ (a.choose 2 : ℝ) by exact_mod_cast hchoose)]
  have ha : (a : ℝ) = (m : ℝ) + (s : ℝ) + 2 := by
    simp [a, m, s, twoCliqueLargeSize]
  have hmle_nat : 2 * m ≤ n := by
    have := Nat.mod_add_div n 2
    omega
  have hmle : 2 * (m : ℝ) ≤ n := by exact_mod_cast hmle_nat
  have htle_nat : s + 2 ≤ n := by
    have := offset_fits n hn
    omega
  have htle : (s : ℝ) + 2 ≤ n := by exact_mod_cast htle_nat
  have hsnon : (0 : ℝ) ≤ s := by positivity
  have hnnon : (0 : ℝ) ≤ n := by positivity
  have hanon : (0 : ℝ) ≤ a := by positivity
  have haupper : (a : ℝ) ≤ (n : ℝ) / 2 + ((s : ℝ) + 2) := by
    linarith
  have hsquare : (a : ℝ) ^ 2 ≤
      ((n : ℝ) / 2 + ((s : ℝ) + 2)) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) / 2 + ((s : ℝ) + 2) - a by linarith)
      (show 0 ≤ (n : ℝ) / 2 + ((s : ℝ) + 2) + a by positivity)]
  have htsquare : ((s : ℝ) + 2) ^ 2 ≤ (n : ℝ) * ((s : ℝ) + 2) := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - ((s : ℝ) + 2) by linarith)
      (show 0 ≤ (s : ℝ) + 2 by positivity)]
  rw [choose_two_cast]
  nlinarith

/-- The normalized palette bound, ready for passage to the limit. -/
theorem twoClique_palette_ratio_bound (n : ℕ) (hn : 16 ≤ n) :
    (max ((twoCliqueLargeSize n).choose 2) ((twoCliqueSmallSize n).choose 2) : ℝ) /
        (n : ℝ) ^ 2 ≤
      1 / 8 + ((Nat.sqrt n : ℝ) + 2) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := twoClique_palette_bound n hn
  rw [div_le_iff₀ (pow_pos hnpos 2)]
  have heq :
      (1 / 8 + ((Nat.sqrt n : ℝ) + 2) / n) * (n : ℝ) ^ 2 =
        (n : ℝ) ^ 2 / 8 + n * ((Nat.sqrt n : ℝ) + 2) := by
    field_simp
  rw [heq]
  exact h

/-- The error term in the palette ratio vanishes. -/
theorem twoClique_error_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => ((Nat.sqrt n + 2 : ℕ) : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hsqrt_nat : Filter.Tendsto Nat.sqrt Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro k
    filter_upwards [Filter.eventually_ge_atTop (k * k)] with n hn
    exact Nat.le_sqrt.mpr hn
  have hsqrt_real : Filter.Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hsqrt_nat
  have hInvS : Filter.Tendsto (fun n : ℕ => ((Nat.sqrt n : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt_real
  have hInvN : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper : Filter.Tendsto
      (fun n : ℕ => 1 / (Nat.sqrt n : ℝ) + 2 / (n : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [one_div, div_eq_mul_inv] using hInvS.add (hInvN.const_mul 2)
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hspos_nat : 0 < Nat.sqrt n := by
      have : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
      omega
    have hspos : (0 : ℝ) < Nat.sqrt n := by exact_mod_cast hspos_nat
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsquare : (Nat.sqrt n : ℝ) ^ 2 ≤ n := by
      exact_mod_cast Nat.sqrt_le' n
    have hratio : (Nat.sqrt n : ℝ) / n ≤ 1 / (Nat.sqrt n : ℝ) := by
      apply (div_le_div_iff₀ hnpos hspos).2
      nlinarith
    calc
      ((Nat.sqrt n + 2 : ℕ) : ℝ) / (n : ℝ) =
          (Nat.sqrt n : ℝ) / n + 2 / n := by push_cast; ring
      _ ≤ 1 / (Nat.sqrt n : ℝ) + 2 / n := add_le_add hratio le_rfl

end Erdos809
