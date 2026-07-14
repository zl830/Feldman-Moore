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
theorem isContinuousable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (Borelf : Measurable f) :
    ∃ τ : TopologicalSpace X, PolishSpace X ∧ BorelSpace X ∧ Continuous[τ, _] f ∧ τ ≤ (upgradeStandardBorel X).toTopologicalSpace := by
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

variable {α : Type*} [mα : MeasurableSpace α] [StandardBorelSpace α]
variable {β : Type*} [mβ : MeasurableSpace β] [StandardBorelSpace β]
variable {f : α → β} (fmeas : Measurable f)


include fmeas
/-- Given f : X → Y a Borel function, X and Y standard Borel spaces, either the Cantor space embeds
in a fiber of f or there are countably many partial Borel subfunctions X → Y,  whose graphs cover graph(f).
-/
theorem LN_Borel : (∃ S : Set (Set α),
  (∀ t ∈ S, BorelPartialSection f t) ∧ S.Countable ∧ Set.univ ⊆ ⋃₀ S)
  ∨ ∃ g : (ℕ → Bool) → α, Continuous[_ , (upgradeStandardBorel α ).toTopologicalSpace] g ∧ Function.Injective g
  ∧ ∀ x y : ℕ → Bool, f (g x) = f (g y) := by
  letI := upgradeStandardBorel β
  let Polishβ : PolishSpace β := inferInstance
  letI := upgradeIsCompletelyMetrizable β
  rcases (isContinuousable fmeas) with ⟨αTop, αPolish , αBorel , fCts, Top_consistent⟩
  letI := @upgradeIsCompletelyMetrizable α αTop αPolish.toIsCompletelyMetrizableSpace
  let m₀ : MetricSpace α := inferInstance
  let m₁ : MetricSpace β := inferInstance
  let Topβ: TopologicalSpace β := inferInstance
  have f_metric_cts : @Continuous α β m₀.toUniformSpace.toTopologicalSpace m₁.toUniformSpace.toTopologicalSpace f := by grind
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
end Project

-- hello Zelong
