import MyProject.LusinNovikovFull
import MyProject.CBobjects
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.CoprodI

namespace FeldmanMoore

set_option autoImplicit false


/-- Feldman-Moore in the context of edge-colorings: Suppose G is a Borel graph
    on std Borel X, then G admits a countable Borel edge-coloring
-/



theorem FeldmanMooreEdgeColoring {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {G : SimpleGraph X} (lcbG : lcBGraph G) :
    ∃ (c : ordEdgeSet G → ℕ) , isMeasEdgeCol G c  := sorry

/- Feldman-Moore for CBERs: Suppose that E is a CBER on std Borel X, then there is
    a countable group Γ and a Borel action Γ → X whose orbit equivalence relation is E,
    i.e. x E y iff ∃ γ ∈ Γ (γ * x = y).
-/
open Classical in
theorem FeldmanMoore {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] {E : X → X → Prop} (cberE : cBer E) :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : MeasurableSpace G) (_ : MulAction G X),
    BorelSpace G ∧ @cdGroup G _ _ ∧ MeasurableSMul₂ G X
    ∧ MulAction.orbitRel G X = E
    := by
  let graph := SimpleGraph.fromEdgeSet {x : Sym2 X | ∃ x1 x2 : x , x1 ≠ x2 ∧ E x1 x2}
  rcases cberE with ⟨h1, h2, h3⟩
  have lcbG : lcBGraph graph := by
    constructor
    · constructor
      unfold ordEdgeSet
      unfold graph
      simp only [SimpleGraph.fromEdgeSet]

    · sorry
    · sorry
  have h := FeldmanMooreEdgeColoring lcbG
  rcases h with ⟨c, measc⟩
  let classes : ℕ → Set X := fun n => {x : X | ∃ e : ordEdgeSet graph, c e = n ∧ x = e.1.1}
  let invols : ℕ → X → X := fun n x => if x ∈ classes n ∧ (∃ y : X , graph.Adj x y ∧ (c ⟨(x,y) , ?_⟩ = n)) then sorry
    else x
  swap
  · sorry
  have is_invol : ∀ n : ℕ , Function.Involutive (invols n) := by
    intro n x
    unfold invols
    sorry
  let G := Monoid.CoprodI fun n : ℕ => Multiplicative (ZMod 2)
  let GactX : MulAction G X := MulAction.ofEndHom (Monoid.CoprodI.lift fun n : ℕ => {
    toFun mulZ := match mulZ.toAdd with
      | 0 => id
      | 1 => invols n
    map_one' := rfl
    map_mul' := by
      intro x y
      cases x with | ofAdd zx
      cases y with | ofAdd zy
      match zx, zy with
      | 0, 0 => rfl
      | 0, 1 => rfl
      | 1, 0 => rfl
      | 1, 1 => funext x; symm; apply is_invol n x
  })
  have (n : ℕ) (x : X) : (Monoid.CoprodI.of (i := n) (Multiplicative.ofAdd 1) : G) • x = invols n x := by rfl
  let topG : TopologicalSpace G := ⊥
  have : DiscreteTopology G := by
    exact discreteTopology_iff_forall_isOpen.mpr fun s ↦ trivial
  have discspaceG : discreteSpace G := by
    constructor
    apply this
  have topgroupG : IsTopologicalGroup G := by
    infer_instance
  have discgroupG : discreteGroup G := by
    constructor
    · apply discspaceG
    · apply topgroupG
  have ctblG : Countable G := by
    unfold G
    simp [Monoid.CoprodI]
    sorry
  have cdG : cdGroup G := by

  sorry
