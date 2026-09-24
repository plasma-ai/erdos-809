import Erdos809.SevenCycle.Statement
import Erdos809.SevenCycle.NearBipartiteCycles

/-!
# Rainbow seven-cycles under vertex relabeling

Pulling an edge coloring back along a vertex equivalence preserves the
rainbow condition on simple seven-cycles.
-/

namespace Erdos809

variable {W V K : Type*}

/-- A rainbow seven-cycle coloring remains rainbow after relabeling vertices. -/
theorem everySevenCycleRainbowOn_comap
    (e : W ≃ V) (G : SimpleGraph V) (C : G.EdgeLabeling K)
    (hRainbow : EverySevenCycleRainbowOn G C) :
    EverySevenCycleRainbowOn (G.comap e)
      (C.pullback (SimpleGraph.Embedding.comap e.toEmbedding G)) := by
  intro q hq hAdj
  have hq' : Function.Injective (fun i : Fin 7 => e (q i)) :=
    e.injective.comp hq
  have hAdj' : ∀ i : Fin 7, G.Adj (e (q i)) (e (q (i + 1))) := by
    intro i
    exact hAdj i
  have h := hRainbow (fun i => e (q i)) hq' hAdj'
  have hlabels (i : Fin 7) :
      (C.pullback (SimpleGraph.Embedding.comap e.toEmbedding G)).get
          (q i) (q (i + 1)) (hAdj i) =
        C.get (e (q i)) (e (q (i + 1))) (hAdj' i) := by
    rfl
  simpa only [hlabels] using h

end Erdos809
