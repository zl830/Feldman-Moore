import MyProject.LusinNovikovFull
import MyProject.CBobjects
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace FeldmanMoore

set_option autoImplicit false



open PolishSpace


/-- Feldman-Moore Edge colouring for the Cantor space -/
theorem FM_edgeCol_Cantor
  {G : SimpleGraph (ℕ → Bool)} (lcbG : lcBGraph G) :
    ∃ (c : ordEdgeSet G → ℕ) , isMeasEdgeCol G c  := sorry

variable {α : Type} (s : Set α)
#check (s : Type)
#check {a : α // a ∈ s}

/-- Feldman-Moore in the context of edge-colorings: Suppose G is a Borel graph
    on std Borel X, then G admits a countable Borel edge-coloring
-/
theorem FeldmanMooreEdgeColoring_uncountable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (hNotCtbl : ¬Countable X)
  {G : SimpleGraph X} (lcbG : lcBGraph G) :
    ∃ (c : ordEdgeSet G → ℕ) , isMeasEdgeCol G c  := by
    let C := (ℕ → Bool)
    have isoC : X ≃ᵐ (ℕ → Bool) := measurableEquivNatBoolOfNotCountable hNotCtbl

    -- H is the graph on C via isoC
    let H := SimpleGraph.map isoC.toEmbedding G
    -- need to show H is locally countable Borel
    have lcbH : lcBGraph H := sorry


    -- using the Cantor FM-colouring version
    let C_edgeCol := (FM_edgeCol_Cantor lcbH)
    rcases C_edgeCol with ⟨cH, hcH⟩

    -- cG : ordEdgeSet G → ℕ given by ordEdgeSet G → ordEdgeSet H → ℕ
    let GtoH : ordEdgeSet G → ordEdgeSet H := fun (x : ordEdgeSet G) =>
    ⟨(isoC.toEmbedding x.1.1 , isoC.toEmbedding x.1.2), ?_⟩
    let cG : ordEdgeSet G → ℕ := cH ∘ GtoH
    rcases hcH with ⟨h1, h2⟩
    · use cG
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro p q hpq
        rcases hpq with ⟨com , notsame⟩

        rcases com with case1 | case2 | case3 | case4
        unfold cG
        simp only [Function.comp_apply, ne_eq]
        unfold GtoH
        apply h1.1
        grind
        --
        unfold cG
        simp only [Function.comp_apply, ne_eq]
        unfold GtoH
        apply h1.1
        grind
        --
        unfold cG
        simp only [Function.comp_apply, ne_eq]
        unfold GtoH
        apply h1.1
        grind
        --
        unfold cG
        simp only [Function.comp_apply, ne_eq]
        unfold GtoH
        apply h1.1
        grind
        --
      · intro p q hpq
        unfold cG
        simp only [Function.comp_apply]
        unfold GtoH
        apply h1.2
        grind
      · unfold cG
        have h3 : Measurable GtoH := by
          let hMeas := Measurable.prodMap isoC.measurable isoC.measurable
          --have hEqual : GtoH = (isoC.measurable.comp measurable_fst).prodMk (isoC.measurable.comp measurable_snd) := sorry
          sorry
        apply Measurable.fun_comp h2 h3
    · unfold ordEdgeSet
      change (SimpleGraph.map isoC.toEmbedding G).Adj (isoC.toEmbedding x.1.1) (isoC.toEmbedding x.1.2)
      rw [SimpleGraph.map_adj]
      use x.1.1, x.1.2
      simp only [Function.Embedding.coeFn_mk, MeasurableEquiv.coe_toEquiv, and_self, and_true]
      exact x.property



/- Feldman-Moore for CBERs: Suppose that E is a CBER on std Borel X, then there is
    a countable group Γ and a Borel action Γ → X whose orbit equivalence relation is E,
    i.e. x E y iff ∃ γ ∈ Γ (γ * x = y).
-/
theorem FeldmanMoore {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] {E : X → X → Prop} (cberE : cBer E) :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : MeasurableSpace G) (_ : MulAction G X),
    BorelSpace G ∧ @cdGroup G _ _ ∧ MeasurableSMul₂ G X
    ∧ MulAction.orbitRel G X = E
    := by sorry
