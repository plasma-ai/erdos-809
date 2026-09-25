import Erdos809.BucicChenMa.Statement
import Erdos809.TwoClique.Arithmetic

/-!
# The uniform error in the two-clique construction

The construction below needs an error of order `n√n`, which is `o(n²)`.
-/

namespace Erdos809.BucicChenMa

/-- The explicit palette error can be absorbed into `ε n²` for large `n`. -/
theorem upperError_eventually_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      3 * (n : ℝ) * ((Nat.sqrt n : ℝ) + 2) ≤ ε * (n : ℝ) ^ 2 := by
  have ht : Filter.Tendsto
      (fun n : ℕ => 3 * (((Nat.sqrt n + 2 : ℕ) : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using Erdos809.twoClique_error_tendsto_zero.const_mul 3
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      3 * (((Nat.sqrt n + 2 : ℕ) : ℝ) / (n : ℝ)) < ε :=
    ht.eventually (eventually_lt_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hsmall : 3 * (((Nat.sqrt n + 2 : ℕ) : ℝ) / (n : ℝ)) < ε :=
    hN n (by omega)
  have hsmall'' : 3 * ((Nat.sqrt n : ℝ) + 2) / (n : ℝ) < ε := by
    convert hsmall using 1
    push_cast
    ring
  have hsmall' : 3 * ((Nat.sqrt n : ℝ) + 2) < ε * (n : ℝ) :=
    (div_lt_iff₀ hnpos).mp hsmall''
  nlinarith

end Erdos809.BucicChenMa
