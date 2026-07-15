/-
Copyright (c) 2026 Zelong Li. All rights reserved.
Author: Zelong Li and Ran Tao
-/


import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic
import MyProject.LusinNovikov

/-!
  Project for ICARM Summer School
-/
namespace Project
open scoped Topology

/-- Given standard Borel space X and Polish Y and Borel f:X → Y, there is a compatible
  Polish topology on X that renders f continuous.
-/
theorem isContinuousable {X Y : Type*} [MeasurableSpace X] [TopX : TopologicalSpace X]
    [PolishSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {f : X → Y} (Borelf : Measurable f) :
    ∃ τ : TopologicalSpace X, PolishSpace X ∧ BorelSpace X ∧ Continuous[τ, _] f ∧ τ ≤ TopX := by
  have ctblBasis := TopologicalSpace.exists_seq_basis Y
  letI := upgradeStandardBorel X
  let t₀ : TopologicalSpace X := inferInstance
  have hPolish : PolishSpace X := inferInstance
  have t₀Borel : BorelSpace X := inferInstance
  rcases ctblBasis with ⟨basis, hbasis⟩
  have clopenPreimage (n : ℕ) : PolishSpace.IsClopenable (f ⁻¹' basis n) := by
    apply MeasurableSet.isClopenable
    apply MeasurableSet.preimage (hbasis.isOpen (Set.mem_range_self n)).measurableSet Borelf
  choose t htt₀ htpolish htclosed htopen using clopenPreimage
  let t (o : Option ℕ) : TopologicalSpace X := o.elim t₀ t
  let τ : TopologicalSpace X := iInf t
  use τ
  have hτPolish : PolishSpace X := by
    apply PolishSpace.iInf
    · use none
      intro i
      cases i
      · rfl
      · exact htt₀ _
    · intro i
      cases i
      · apply hPolish
      · apply htpolish
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hτPolish
  · constructor
    rw [t₀Borel.measurable_eq]
    symm
    apply MeasureTheory.borel_eq_borel_of_le
    · exact hτPolish
    · exact hPolish
    · apply iInf_le t none
  · rw [hbasis.continuous_iff, Set.forall_mem_range]
    intro i
    refine IsOpen.mono (htopen i) ?_
    apply iInf_le t (some i)
  · apply iInf_le t none


open LusinNovikov
open TopologicalSpace


variable {α : Type*} [mα : MeasurableSpace α] [TopologicalSpace α] [PolishSpace α] [BorelSpace α]
variable {β : Type*} [mβ : MeasurableSpace β] [StandardBorelSpace β]
variable {f : α → β} (fmeas : Measurable f)

include fmeas in
/-- Lusin-Novikov for Borel functions
-/
theorem LN_BorelFunction : (∃ S : Set (Set α),
  (∀ t ∈ S, BorelPartialSection f t) ∧ S.Countable ∧ Set.univ ⊆ ⋃₀ S)
  ∨ ∃ g : (ℕ → Bool) → α, Continuous g ∧ Function.Injective g
  ∧ ∀ x y : ℕ → Bool, f (g x) = f (g y) := by
  letI := upgradeStandardBorel β
  let Polishβ : PolishSpace β := inferInstance
  letI := upgradeIsCompletelyMetrizable β
  rcases (isContinuousable fmeas) with ⟨αTop, αPolish , αBorel , fCts, Top_consistent⟩
  letI := @upgradeIsCompletelyMetrizable α αTop αPolish.toIsCompletelyMetrizableSpace
  let m₀ : MetricSpace α := inferInstance
  let m₁ : MetricSpace β := inferInstance
  let Topβ: TopologicalSpace β := inferInstance
  have f_metric_cts : @Continuous α β m₀.toUniformSpace.toTopologicalSpace
    m₁.toUniformSpace.toTopologicalSpace f := by grind
  rcases (lusin_novikov f_metric_cts) with _ | ⟨g, gCts, gInj, gSect⟩
  · grind
  · right
    use g
    refine ⟨?_, gInj, gSect⟩
    have same_top_α : m₀.toUniformSpace.toTopologicalSpace = αTop := by grind
    --have : m₁.toUniformSpace.toTopologicalSpace = Topβ := by grind
    rw [same_top_α] at gCts
    have := (continuous_le_rng Top_consistent gCts)
    assumption


/-- X,Y std Borel spaces, f : X → Y is Borel if graph(f) is analytic.
-/
theorem fun_borel_if_analytic {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [PolishSpace X] [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [PolishSpace Y]
    {f : X → Y} (anal_graph : MeasureTheory.AnalyticSet (Set.graphOn f Set.univ)) :
    Measurable f := by
  let G := Set.graphOn f Set.univ
  have (A : Set Y) (MeasA : MeasurableSet A) : MeasureTheory.AnalyticSet (f ⁻¹' A) := by
    have h₁ : ∀ x : X, (x ∈ f⁻¹' A) ↔ (∃ y : Y, f x = y ∧ y ∈ A) := by grind
    have h₂ : f⁻¹' A = Prod.fst '' (Prod.snd⁻¹' A ∩ G) := by
      ext
      constructor
      · simp [h₁, G]
      · simp [h₁, G]
    rw [h₂]
    apply MeasureTheory.AnalyticSet.image_of_continuous
    · rw [Set.inter_eq_iInter]
      apply MeasureTheory.AnalyticSet.iInter
      intro b
      cases b
      · exact anal_graph
      · apply MeasurableSet.analyticSet
        apply MeasA.preimage
        fun_prop
    · fun_prop
  intro A MeasA
  apply MeasureTheory.AnalyticSet.measurableSet_of_compl
  · apply this A MeasA
  · rw [← Set.preimage_compl]
    apply this
    exact MeasA.compl

/-- Lusin Novikov for Borel sets
-/
theorem FullLusinNovikov {X Y : Type*} [Nonempty X] [Nonempty Y] [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X]
    [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {A : Set (X × Y)} (BorelA : MeasurableSet A) : Or (∃ F : ℕ → X → Y, (∀ n, Measurable (F n))∧
    A ⊆ ⋃ n, {p : X × Y | F n p.1 = p.2}) (∃ x : X, (∃ g : (ℕ → Bool) → {y : Y | (x,y) ∈ A},
    Continuous g ∧ Function.Injective g)) := by
  let f : A → X := fun p => p.1.1
  have Measf : Measurable f := by
    unfold f
    fun_prop
  have StdBorelA := BorelA.standardBorel
  let subspaceTop : TopologicalSpace A := inferInstance
  letI := upgradeStandardBorel A
  let t₀ : TopologicalSpace A := (upgradeStandardBorel A).toTopologicalSpace
  have hPolish : PolishSpace A := inferInstance
  have t₀Borel : BorelSpace A := inferInstance
  have finerTop := @Measurable.exists_continuous A A t₀ _ _ _ subspaceTop _ _ id _ measurable_id
  rcases finerTop with ⟨τ, fineτ, contτ, Polishτ⟩
  have Borelτ : @BorelSpace A τ _ := by
    constructor
    rw [MeasureTheory.borel_eq_borel_of_le Polishτ hPolish fineτ, t₀Borel.measurable_eq]
  have h₁ := @LN_BorelFunction A _ _ Polishτ Borelτ X _ _ f Measf
  rcases h₁ with h₂ | h₃
  · left
    rcases h₂ with ⟨S, hS₁, hS₂, hS₃⟩
    rcases Set.eq_empty_or_nonempty S with empty | nonempty
    · rw [empty] at hS₃
      simp at hS₃
      use fun n x => Classical.arbitrary Y
      simp [hS₃]
    · have enum := hS₂.exists_eq_range nonempty
      rcases enum with ⟨enum, rfl⟩
      rw [Set.forall_mem_range] at hS₁
      unfold BorelPartialSection at hS₁
      classical
      let G (n : ℕ) : f '' enum n → Y := fun x => x.2.choose.1.2
      let const (n : ℕ) : ((f '' enum n)ᶜ : Set X) → Y := fun x => Classical.arbitrary Y
      let F : ℕ → X → Y := fun n x => if defined : x ∈ f '' enum n
        then G n ⟨x, defined⟩ else const n ⟨x, defined⟩
      use F
      constructor
      · intro n
        unfold F
        apply Measurable.dite
        · have boreln : MeasurableSet (f '' enum n) := by
            apply MeasurableSet.image_of_measurable_injOn
            apply (hS₁ n).left
            sorry
          letI := upgradeStandardBorel (f '' enum n)
          sorry
        · unfold const
          fun_prop
        · apply MeasurableSet.image_of_measurable_injOn
          · apply (hS₁ n).left
          · apply Measf
          · apply (hS₁ n).right
      · intro p pA
        specialize hS₃ (Set.mem_univ ⟨p, pA⟩)
        rw [Set.mem_sUnion] at hS₃
        rcases hS₃ with ⟨t, inenum, int⟩
        rw [Set.mem_range] at inenum
        rcases inenum with ⟨n, rfl⟩
        rw [Set.mem_iUnion]
        use n
        rw [Set.mem_setOf]
        unfold F
        have h : p.1 ∈ f '' enum n := by
          rw [Set.mem_image]
          use ⟨p, pA⟩
        rw [dif_pos h]
        unfold G
        generalize_proofs p₂
        have pchoose := p₂.choose_spec
        rw [(hS₁ n).right pchoose.1 int pchoose.2]
  · right
    rcases h₃ with ⟨g, contg, injg, fiberg⟩
    use f (g (Classical.arbitrary (ℕ → Bool)))
    let g' : (ℕ → Bool) → {y | (f (g (Classical.arbitrary (ℕ → Bool))), y) ∈ A} := fun s =>
      ⟨(g s).1.2, by simp only [fiberg _ s, Set.mem_setOf_eq]; exact (g s).2⟩
    use g'
    constructor
    · have contg' := @Continuous.comp _ _ _ (_) (_) (_) _ _ contτ contg
      unfold g'
      rw [Topology.IsInducing.subtypeVal.continuous_iff]
      dsimp [Function.comp_def]
      apply Continuous.snd
      apply Continuous.subtype_val
      exact contg'
    · intro s₁ s₂ g'sseq
      apply injg
      ext
      · apply fiberg
      · unfold g' at g'sseq
        apply congrArg Subtype.val g'sseq




end Project
