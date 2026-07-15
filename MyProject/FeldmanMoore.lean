import MyProject.LusinNovikovFull
import MyProject.CBobjects
namespace FeldmanMoore

/-- Feldman-Moore in the context of edge-colorings: Suppose G is a Borel graph
    on std Borel X, then G admits a countable Borel edge-coloring
-/
theorem FeldmanMooreEdgeColoring {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] {G : SimpleGraph X} (lcbG : lcBGraph G):
    ∃ c : G.edgeSet → ℕ, (isMeasEdgeCol c G) :=
  sorry

/-- Feldman-Moore for CBERs: Suppose that E is a CBER on std Borel X, then there is
    a countable group Γ and a Borel action Γ → X whose orbit equivalence relation is E,
    i.e. x E y iff ∃ γ ∈ Γ (γ * x = y).
-/
theorem FeldmanMoore {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] {E : X → X → Prop} (cberE : cBer E) :
    sorry :=
    sorry
