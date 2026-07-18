
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic
import MyProject.LusinNovikov
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Topology.Separation.Hausdorff

open TopologicalSpace

/-- X,Y std Borel spaces, f : X → Y is Borel if graph(f) is analytic.
-/
theorem fun_borel_if_graphAnalytic {X Y : Type*}
[MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
[PolishSpace X] [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]
{f : X → Y} (analytic_graph : MeasureTheory.AnalyticSet (Set.graphOn f Set.univ)) :
    Measurable f := by
  let graph := Set.graphOn f Set.univ
  /- preimage of measurable is measurable-/
  have (A : Set Y) (MeasA : MeasurableSet A) : MeasureTheory.AnalyticSet (f ⁻¹' A) := by
    have h₁ : ∀ x : X, (x ∈ f⁻¹' A) ↔ (∃ y : Y, f x = y ∧ y ∈ A) := by grind
    have h₂ : f⁻¹' A = Prod.fst '' (Prod.snd⁻¹' A ∩ graph) := by
      ext
      constructor
      · simp [h₁, graph]
      · simp [h₁, graph]
    rw [h₂]
    apply MeasureTheory.AnalyticSet.image_of_continuous
    · rw [Set.inter_eq_iInter]
      apply MeasureTheory.AnalyticSet.iInter
      intro b
      cases b
      · exact analytic_graph
      · apply MeasurableSet.analyticSet
        apply MeasA.preimage
        fun_prop
    · fun_prop
  /- concluding-/
  intro A MeasA
  apply MeasureTheory.AnalyticSet.measurableSet_of_compl
  · apply this A MeasA
  · rw [← Set.preimage_compl]
    apply this
    exact MeasA.compl


/-- for f: X → Y, for Hausdorff second-countable Y with countable basis V,
 graph(f) = {(x,y) | ∀ n : ℕ , y ∈ V n ↔ x ∈ Set.preimage f (V n)} -/
theorem graph_equivalence {X Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [T2Space Y]
(f : X → Y) (V : Set (Set Y)) (hV : IsTopologicalBasis V) :
(Set.graphOn f Set.univ) = {x : X × Y | ∀ v ∈ V , x.1 ∈ Set.preimage f v ↔ x.2 ∈ v } := by
  ext x
  constructor
  · unfold Set.graphOn
    grind
  · unfold Set.graphOn
    intro hx
    simp only [Set.image_univ, Set.mem_range]
    use x.1
    ext
    · grind
    · simp only
      by_contra
      let h1 := t2_separation this
      rcases h1 with ⟨u, ⟨v, ⟨openu, ⟨openv, ⟨fx1u , x2v ,disjointuv⟩⟩⟩⟩⟩
      simp at hx
      let h2 := IsTopologicalBasis.exists_subset_of_mem_open hV x2v openv
      rcases h2 with ⟨w, ⟨wBasic , x2w , wsubv⟩⟩
      have h3 : f x.1 ∉ w := by
        grind
      grind


/-- X, Y standard Borel spaces, if f : X → Y is Borel function then graph(f) is borel. -/
theorem measurableSet_graph' {X Y : Type*} [MeasurableSpace X]
[MeasurableSpace Y] [TopologicalSpace Y] [SecondCountableTopology Y] [BorelSpace Y] [T2Space Y]
  {f : X → Y} (measf : Measurable f) : MeasurableSet (Set.graphOn f Set.univ) := by

  let graph := (Set.graphOn f Set.univ)
  /- exhibit countable basis V-/
  let haveCtnlBasis := TopologicalSpace.exists_seq_basis Y
  rcases haveCtnlBasis with ⟨V , hV⟩
  /- sets in V are open and measurable-/
  have h4 : ∀ n : ℕ, IsOpen (V n) := by intro n; exact hV.isOpen (by exact ⟨n, rfl⟩)
  have h8 : ∀ n : ℕ, MeasurableSet (V n) := by intro n; apply IsOpen.measurableSet (h4 n)
  /- an equivalent way of saying "graph"-/
  have hIff3 : ∀ x : X × Y, x ∈ graph ↔ ∀ n : ℕ , x.2 ∈ V n ↔ x.1 ∈ Set.preimage f (V n) := by
    have hV1 : IsTopologicalBasis (Set.range V) := by grind
    let h6 := graph_equivalence f (Set.range V) hV1
    grind
  let A (n : ℕ ) : Set (X × Y) := { x : X × Y | x.1 ∈ Set.preimage f (V n) ↔ x.2 ∈ (V n)}
  have hIff2 : graph = (⋂ n : ℕ, A n) := by
    have h5 : (⋂ n : ℕ, A n) =
    { x : X × Y | ∀ n : ℕ, x.1 ∈ Set.preimage f (V n) ↔ x.2 ∈ (V n)} := by
      ext x
      simp [A]
    grind
  /-A n are measurable-/
  have measA : ∀ n : ℕ, MeasurableSet (A n) := by
    intro n
    refine MeasurableSet.iff ?_ ?_
    · have h1 : MeasurableSet (f⁻¹' V n) := by
        have h3 : MeasurableSet (V n) := by
          apply IsOpen.measurableSet (h4 n)
        measurability
      have h2 : {x | x.1 ∈ f ⁻¹' V n} = (f ⁻¹' V n) ×ˢ (Set.univ : Set Y) := by grind
      measurability
    · have h7 : {x | x.2 ∈ V n} = (Set.univ : Set X) ×ˢ V n := by grind
      measurability
  /- concluding-/
  have measGraph : MeasurableSet graph := by
    rw [hIff2]
    apply MeasurableSet.iInter measA
  assumption

/-- A function f: X → Y between standard Borel spaces is Borel
iff its graph is analytic (iff its graph is Borel). -/
theorem analyticSet_graph_iff_Borel_function {X Y : Type*}
  [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [PolishSpace X]
  [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]
  {f : X → Y} : Measurable f ↔  MeasureTheory.AnalyticSet (Set.graphOn f Set.univ) := by
  let graph := (Set.graphOn f Set.univ)
  constructor
  · intro measf
    have borelGraph : MeasurableSet graph  := measurableSet_graph' measf
    apply _root_.MeasurableSet.analyticSet borelGraph
  · intro graphAnalytic
    apply fun_borel_if_graphAnalytic graphAnalytic
