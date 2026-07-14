/-
Copyright (c) 2026 Zelong Li. All rights reserved.
Author: Zelong Li
-/


import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic
/-!
  Project for ICARM Summer School
-/
namespace Project

/-- Given standard Borel space X and Polish Y and Borel f:X → Y, there is a compatible
  Polish topology on X that renders f continuous.
-/
theorem isContinuousable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (Borelf : Measurable f) :
    ∃ _ : TopologicalSpace X, PolishSpace X ∧ BorelSpace X ∧ Continuous f := by
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
  refine ⟨?_, ?_, ?_⟩
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


end Project
