import Erdos809.Statement
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card

/-!
# Restricting a rainbow coloring to an exact number of edges

Deleting edges cannot create a seven-cycle or change the colors of the edges
that remain. This lets an upper-bound construction with at least the prescribed
number of edges be trimmed to the exact edge count.
-/

namespace Erdos809

/-- Any number of edges up to the size of a rainbow-colored graph can be kept,
with the inherited coloring still rainbow on every seven-cycle. -/
theorem rainbow_subgraph_exact_edges {n k m : ℕ}
    (G : SimpleGraph (Fin n)) (C : G.EdgeLabeling (Fin k))
    (hC : EverySevenCycleRainbow G C)
    (hm : m ≤ Nat.card G.edgeSet) :
    ∃ (H : SimpleGraph (Fin n)), H ≤ G ∧ Nat.card H.edgeSet = m ∧
      ∃ (D : H.EdgeLabeling (Fin k)), EverySevenCycleRainbow H D := by
  classical
  have hm' : m ≤ G.edgeFinset.card := by
    simpa [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card] using hm
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := G.edgeFinset) hm'
  let H : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (s : Set (Sym2 (Fin n)))
  have hHedge : H.edgeSet = (s : Set (Sym2 (Fin n))) := by
    ext e
    simp only [H, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff]
    constructor
    · exact And.left
    · intro he
      exact ⟨he, by
        simpa only [Sym2.mem_diagSet] using
          G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hs he))⟩
  have hHG : H ≤ G := by
    apply SimpleGraph.edgeSet_subset_edgeSet.mp
    rw [hHedge]
    intro e he
    exact SimpleGraph.mem_edgeFinset.mp (hs he)
  have hHcard : Nat.card H.edgeSet = m := by
    rw [Nat.card_coe_set_eq, hHedge, Set.ncard_coe_finset, hcard]
  let D : H.EdgeLabeling (Fin k) := C.pullback (SimpleGraph.Hom.ofLE hHG)
  refine ⟨H, hHG, hHcard, D, ?_⟩
  intro v hv h
  have hG : ∀ i : Fin 7, G.Adj (v i) (v (i + 1)) := fun i => hHG (h i)
  have hRainbow := hC v hv hG
  have hcolor (i : Fin 7) :
      D.get (v i) (v (i + 1)) (h i) = C.get (v i) (v (i + 1)) (hG i) := by
    rfl
  simpa only [hcolor] using hRainbow

end Erdos809
