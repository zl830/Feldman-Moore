module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

public section

variable {X Y : Type*}
  [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [PolishSpace X]
  [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]

/-- Preimage of a Borel set under a function whose graph is analytic is analytic. -/
lemma analyticSet_preimage_of_measurableSet_of_analyticSet_graph
    {f : X → Y} (analytic_graph : MeasureTheory.AnalyticSet {(x, y) : X × Y | y = f x})
    {A : Set Y} (MeasA : MeasurableSet A) :
    MeasureTheory.AnalyticSet (f ⁻¹' A) := by
  have h₁ : ∀ x : X, (x ∈ f⁻¹' A) ↔ (∃ y : Y, f x = y ∧ y ∈ A) := by grind
  have h₂ : f⁻¹' A = Prod.fst '' (Prod.snd⁻¹' A ∩ { (x, y) : X × Y | y = f x }) :=
    by ext; simp [h₁]
  rw [h₂]
  apply MeasureTheory.AnalyticSet.image_of_continuous
  · rw [Set.inter_eq_iInter]
    apply MeasureTheory.AnalyticSet.iInter
    rintro (_ | _)
    · exact analytic_graph
    · apply MeasurableSet.analyticSet
      apply MeasA.preimage
      fun_prop
  · fun_prop

/-- A map between two standard Borel spaces is Borel if its graph is analytic. -/
@[fun_prop]
theorem measurable_of_analyticSet_graph
    {f : X → Y} (analytic_graph : MeasureTheory.AnalyticSet {(x, y) : X × Y | y = f x}) :
    Measurable f := by
  /- We'll prove that preimage of measurable set is measurable. -/
  intro A MeasA
  apply MeasureTheory.AnalyticSet.measurableSet_of_compl
  · apply analyticSet_preimage_of_measurableSet_of_analyticSet_graph analytic_graph MeasA
  · rw [← Set.preimage_compl]
    apply analyticSet_preimage_of_measurableSet_of_analyticSet_graph analytic_graph MeasA.compl


theorem TopologicalSpace.IsTopologicalBasis.eq_iff_all_mem_iff {X : Type*}
    [TopologicalSpace X] [T1Space X]
    {V : Set (Set X)} (hV : IsTopologicalBasis V)
    (a b : X) :
    a = b ↔ ∀ v ∈ V, a ∈ v ↔ b ∈ v := by
  constructor
  · grind
  · contrapose
    intro ne
    have := hV.exists_mem_of_ne ne
    grind


theorem TopologicalSpace.IsTopologicalBasis.graph_eq {X Y : Type*}
    [TopologicalSpace Y] [T1Space Y]
    {V : Set (Set Y)} (hV : IsTopologicalBasis V)
    (f : X → Y) :
    { (x, y) : X × Y | y = f x } = { (x, y) : X × Y | ∀ v ∈ V , x ∈ f ⁻¹' v ↔ y ∈ v } := by
  ext x
  have := hV.eq_iff_all_mem_iff (f x.1) x.2
  grind [Set.graphOn, Set.image_univ]


/-- A measurable function into a countably separated space has a measurable graph. -/
@[measurability]
theorem measurableSet_graph {X Y : Type*}
    [MeasurableSpace X]
    [MeasurableSpace Y] [cs : MeasurableSpace.CountablySeparated Y]
    {f : X → Y} (measf : Measurable f) :
    MeasurableSet { (x, y) : X × Y | y = f x } := by
  let ⟨V, Vctbl, Vmeas, Vsep⟩ := cs.countably_separated
  let A : Set (Set (X × Y)) := (fun v => { (x, y) : X × Y | x ∈ f ⁻¹' v ↔ y ∈ v }) '' V
  have : { (x, y) : X × Y | y = f x } = ⋂₀ A := by
    ext x
    have := Vsep (f x.1) (Set.mem_univ _) x.2 (Set.mem_univ _)
    simp [A]; grind
  rw [this]
  apply MeasurableSet.sInter (Vctbl.image _)
  intro
  measurability -- TODO very slow.


/-- A function f: X → Y between standard Borel spaces is Borel
iff its graph is analytic (iff its graph is Borel). -/
theorem analyticSet_graph_iff_measurable {X Y : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [PolishSpace X]
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]
    (f : X → Y) :
    Measurable f ↔ MeasureTheory.AnalyticSet { (x, y) : X × Y | y = f x } := by
  constructor
  · intro
    apply MeasurableSet.analyticSet
    measurability
  · measurability
