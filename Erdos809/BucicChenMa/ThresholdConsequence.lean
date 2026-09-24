import Erdos809.BucicChenMa.Statement
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The threshold consequence of the Bucić–Chen–Ma formula

The theorem's uniform error estimate applies to the first edge count above
`⌊n²/4⌋`. At that count, the square-root contribution is at most linear in
`n`, so it disappears after division by `n²`.
-/

namespace Erdos809.BucicChenMa

private theorem threshold_edge_feasible (n : ℕ) (hn : 4 ≤ n) :
    n * n / 4 + 1 ≤ n.choose 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  have hfloor : 4 * (n * n / 4) ≤ n * n := Nat.mul_div_le _ _
  have hnm : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h : n - 1 + 1 = n := by omega
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast h
    linarith
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hpoly : n * n + 4 ≤ 2 * (n * (n - 1)) := by
    have hfactor : 0 ≤ ((n : ℝ) - 4) * ((n : ℝ) + 2) :=
      mul_nonneg (by linarith) (by positivity)
    have hreal : ((n * n + 4 : ℕ) : ℝ) ≤ ((2 * (n * (n - 1)) : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast hreal
  omega

private theorem threshold_mainTerm_bound (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ mainTerm n (n * n / 4 + 1) / (n : ℝ) ^ 2 - 1 / 8 ∧
      mainTerm n (n * n / 4 + 1) / (n : ℝ) ^ 2 - 1 / 8 ≤ 1 / (n : ℝ) := by
  have hmod := Nat.mod_add_div (n * n) 4
  have hmodlt : n * n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hdecomp : (n : ℝ) ^ 2 =
      4 * ((n * n / 4 : ℕ) : ℝ) + ((n * n % 4 : ℕ) : ℝ) := by
    have hcast : (((n * n % 4 + 4 * (n * n / 4) : ℕ) : ℝ)) =
        ((n * n : ℕ) : ℝ) := by exact_mod_cast hmod
    push_cast at hcast
    nlinarith
  have hmodreal : ((n * n % 4 : ℕ) : ℝ) < 4 := by exact_mod_cast hmodlt
  have hedge_lo : (n : ℝ) ^ 2 / 4 ≤ ((n * n / 4 + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hedge_hi : ((n * n / 4 + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 4 + 1 := by
    push_cast
    have hmodnonneg : 0 ≤ ((n * n % 4 : ℕ) : ℝ) := by positivity
    nlinarith
  let D : ℝ := ((n * n / 4 + 1 : ℕ) : ℝ) - (n : ℝ) ^ 2 / 4
  have hD0 : 0 ≤ D := by dsimp [D]; linarith
  have hD1 : D ≤ 1 := by dsimp [D]; linarith
  have hsqrt0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hsqrt1 : Real.sqrt D ≤ 1 := (Real.sqrt_le_one).2 hD1
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
  have hmain_lo : (n : ℝ) ^ 2 / 8 ≤ mainTerm n (n * n / 4 + 1) := by
    dsimp [mainTerm]
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) / 2 by positivity) hsqrt0]
  have hmain_hi : mainTerm n (n * n / 4 + 1) ≤ (n : ℝ) ^ 2 / 8 + (n : ℝ) := by
    dsimp [mainTerm]
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) / 2 by positivity)
      (sub_nonneg.mpr hsqrt1)]
  constructor
  · have h : (1 / 8 : ℝ) ≤ mainTerm n (n * n / 4 + 1) / (n : ℝ) ^ 2 := by
      apply (le_div_iff₀ hn2).2
      nlinarith
    linarith
  · calc
      mainTerm n (n * n / 4 + 1) / (n : ℝ) ^ 2 - 1 / 8 =
          (mainTerm n (n * n / 4 + 1) - (n : ℝ) ^ 2 / 8) / (n : ℝ) ^ 2 := by
            field_simp
      _ ≤ (n : ℝ) / (n : ℝ) ^ 2 :=
        (div_le_div_iff_of_pos_right hn2).2 (by linarith)
      _ = 1 / (n : ℝ) := by field_simp

private theorem threshold_mainTerm_tendsto :
    Filter.Tendsto
      (fun n : ℕ => mainTerm n (n * n / 4 + 1) / (n : ℝ) ^ 2)
      Filter.atTop (nhds (1 / 8 : ℝ)) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 1 / (n : ℝ) < ε :=
    tendsto_one_div_atTop_nhds_zero_nat.eventually (eventually_lt_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hb := threshold_mainTerm_bound n (by omega : 1 ≤ n)
  rw [Real.dist_eq, abs_of_nonneg hb.1]
  exact lt_of_le_of_lt hb.2 (hN n (by omega))

/-- For a fixed odd cycle, the uniform full-density formula implies the
threshold asymptotic. -/
theorem fullDensityFormula_implies_threshold (k : ℕ)
    (h : FullDensityFormula k) : ThresholdFormula k := by
  have hmain := threshold_mainTerm_tendsto
  have herror : Filter.Tendsto
      (fun n : ℕ =>
        ((maximalAntiRamseyCycle n (n * n / 4 + 1) (2 * k + 1) : ℝ) -
          mainTerm n (n * n / 4 + 1)) / (n : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (by linarith)
    refine ⟨max 4 N, ?_⟩
    intro n hn
    have hn4 : 4 ≤ n := by omega
    have hnN : N ≤ n := by omega
    have hbound := hN n hnN (n * n / 4 + 1) (le_refl _)
      (threshold_edge_feasible n hn4)
    have hn2 : 0 < (n : ℝ) ^ 2 := by
      have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hn2]
    have hdiv :
        |(maximalAntiRamseyCycle n (n * n / 4 + 1) (2 * k + 1) : ℝ) -
          mainTerm n (n * n / 4 + 1)| / (n : ℝ) ^ 2 ≤ ε / 2 := by
      calc
        _ ≤ (ε / 2 * (n : ℝ) ^ 2) / (n : ℝ) ^ 2 :=
          (div_le_div_iff_of_pos_right hn2).2 hbound
        _ = ε / 2 := by field_simp
    linarith
  have hsum := herror.add hmain
  change Filter.Tendsto
    (fun n : ℕ =>
      (maximalAntiRamseyCycle n (n * n / 4 + 1) (2 * k + 1) : ℝ) /
        (n : ℝ) ^ 2) Filter.atTop (nhds (1 / 8 : ℝ))
  convert hsum using 1
  · ext n
    ring
  · simp

/-- The published uniform formula implies the threshold limit for every
odd cycle covered by Bucić–Chen–Ma. -/
theorem statement_implies_threshold (h : Statement) : ThresholdStatement := by
  intro k hk
  exact fullDensityFormula_implies_threshold k (h k hk)

end Erdos809.BucicChenMa
