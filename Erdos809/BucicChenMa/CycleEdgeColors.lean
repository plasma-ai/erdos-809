import Erdos809.BucicChenMa.Statement
import Mathlib.Data.Finset.Card

/-!
# Distinct colors forced by a common cycle

The lower-bound proof repeatedly identifies a family of edges such that
every pair appears on one cycle. A rainbow coloring then uses at least one
color for each edge in the family.
-/

namespace Erdos809.BucicChenMa

/-- Two edges of a graph occur on one simple cycle of the chosen length. -/
def TwoEdgesOnCycle {V : Type*} {m : ℕ} [NeZero m]
    (G : SimpleGraph V) (e₁ e₂ : G.edgeSet) : Prop :=
  ∃ (v : Fin m → V) (_hv : Function.Injective v)
      (h : ∀ i : Fin m, G.Adj (v i) (v (i + 1)))
      (i j : Fin m),
    (⟨s(v i, v (i + 1)), h i⟩ : G.edgeSet) = e₁ ∧
      (⟨s(v j, v (j + 1)), h j⟩ : G.edgeSet) = e₂

/-- Two distinct edges on a common rainbow cycle receive different colors. -/
theorem colors_ne_of_twoEdgesOnCycle
    {V : Type*} {m colors : ℕ} [NeZero m]
    (G : SimpleGraph V) (C : G.EdgeLabeling (Fin colors))
    (hRainbow : EveryCycleRainbow m G C)
    {e₁ e₂ : G.edgeSet} (hne : e₁ ≠ e₂)
    (hcycle : TwoEdgesOnCycle (m := m) G e₁ e₂) : C e₁ ≠ C e₂ := by
  obtain ⟨v, hv, hAdj, i, j, hi, hj⟩ := hcycle
  have hij : i ≠ j := by
    intro h
    exact hne (hi.symm.trans (h ▸ hj))
  have hci : C e₁ = C.get (v i) (v (i + 1)) (hAdj i) := by
    change C e₁ = C ⟨s(v i, v (i + 1)), hAdj i⟩
    exact congrArg C hi.symm
  have hcj : C e₂ = C.get (v j) (v (j + 1)) (hAdj j) := by
    change C e₂ = C ⟨s(v j, v (j + 1)), hAdj j⟩
    exact congrArg C hj.symm
  rw [hci, hcj]
  exact (hRainbow v hv hAdj).ne hij

/-- A family of pairwise cocyclic edges has at most as many members as
colors in any rainbow coloring. -/
theorem cocyclic_edge_family_card_le_colors
    {V : Type*} {m colors : ℕ} [NeZero m]
    (G : SimpleGraph V) (C : G.EdgeLabeling (Fin colors))
    (hRainbow : EveryCycleRainbow m G C)
    (A : Finset G.edgeSet)
    (hcycle : ∀ e₁ ∈ A, ∀ e₂ ∈ A, e₁ ≠ e₂ →
      TwoEdgesOnCycle (m := m) G e₁ e₂) :
    A.card ≤ colors := by
  have hinj : (A : Set G.edgeSet).InjOn C := by
    intro e₁ he₁ e₂ he₂ heq
    by_contra hne
    exact (colors_ne_of_twoEdgesOnCycle G C hRainbow hne
      (hcycle e₁ he₁ e₂ he₂ hne)) heq
  have hmap : Set.MapsTo C (A : Set G.edgeSet) (Finset.univ : Finset (Fin colors)) := by
    intro e _
    exact Finset.mem_univ _
  simpa using Finset.card_le_card_of_injOn C hmap hinj

end Erdos809.BucicChenMa
