import MyProject.LusinNovikovFull
import MyProject.CBobjects
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.CoprodI
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Data.Nat.Pairing
import Mathlib.Combinatorics.SimpleGraph.Maps

noncomputable section
namespace FeldmanMoore

set_option autoImplicit false

open PolishSpace
open Project


def leastDiffer : { p : (ℕ → Bool) × (ℕ → Bool) | ∃ (n : ℕ), p.1 n ≠ p.2 n } → ℕ :=
  fun p => Nat.find p.property

theorem leastDiffer_measurable : Measurable leastDiffer := by
  apply measurable_find
  measurability

def cantorOrderRel : { p : (ℕ → Bool) × (ℕ → Bool) | ∃ (n : ℕ), p.1 n ≠ p.2 n } → Prop :=
  fun p => p.1.1 (leastDiffer p) < p.1.2 (leastDiffer p)

theorem nat_bool_uncountable : Uncountable (ℕ → Bool) := by
  rw [uncountable_iff_forall_not_surjective]
  intro f hf
  obtain ⟨b, hb⟩ :=
    Function.exists_fixed_point_of_surjective f hf Bool.not
  cases b <;> simp at hb

open Classical in
/-- Feldman-Moore Edge colouring for the Cantor space -/
theorem FM_edgeCol_Cantor
  {G : SimpleGraph (ℕ → Bool)} (lcbG : lcBGraph G) :
    ∃ (c : ordEdgeSet G → ℕ) , isMeasEdgeCol G c  := by
      let C := (ℕ → Bool)
      have GMeas : MeasurableSet (ordEdgeSet G) := by
        let h := (lcbG.tomeasGraph).Meas
        assumption
      have CstdBorel : StandardBorelSpace C := inferInstance
      let CTop : TopologicalSpace C := (upgradeStandardBorel C).toTopologicalSpace
      have CPolish : PolishSpace C := inferInstance
      let ln := FullLusinNovikov GMeas
      rcases ln with ⟨ F, ⟨ MeasFn, unionFcoversG ⟩ ⟩ | ⟨x, g, _, gInj⟩


      -- F : Nat → C → C , F(n) is a total function C → C,
      -- naming the neighbours of x with n, x in C

      -- define the edge colouring : ordEdgeSet G → ℕ × ℕ × ℕ
      -- d(x,y) = (a,b,c) where F a (x) = y and F b (y) = x and x < y
      -- and c is the least Nat such that c is the first coordinate for which x(c) ≠ y(c)
      -- F0 (x,y) = (n, m) ↔ F n x = y ∧ F m y = x
      · let S : Set (C × C) := {x : C × C | ∃ (n m : ℕ), F n x.1 = x.2 ∧ F m x.2 = x.1}
        have : ∀ x ∈ S, ∃ (n m : ℕ), F n x.1 = x.2 ∧ F m x.2 = x.1 := by simp [S]
        choose fn fm hn hm using this
        let F0 : {x : C × C | ∃ (n m : ℕ), F n x.1 = x.2 ∧ F m x.2 = x.1 } →
        ℕ × ℕ  := fun x => (fn x x.property, fm x x.property)

      -- F1 : (x,y) ↦ (n, m) ↔ F n x = y ∧ F m y = x ∧ x < y
        let F1 (x : ordEdgeSet G) : ℕ × ℕ :=
        if cantorOrderRel ⟨x, sorry⟩ then (F0 ⟨x.1, sorry⟩) else (F0 ⟨x.1.swap, sorry⟩)

        -- F2 : (x,y) ↦ n ↔ n is the least such that x(n) ≠ y(n)
        let F2 (x : ordEdgeSet G) : ℕ := by
          have h4 : ∃ (n : ℕ), x.1.1 n ≠ x.1.2 n := by sorry
          apply leastDiffer ⟨x, h4⟩
        let c (x : ordEdgeSet G) : (ℕ × ℕ) × ℕ := (F1 x, F2 x)
        let bij1 := Equiv.prodCongr Nat.pairEquiv (Equiv.refl ℕ)
        let bij := (Equiv.trans bij1 Nat.pairEquiv)
        use Function.comp bij.toFun c
        refine ⟨?_ , ?_⟩

        -- the composition is an edge colouring
        · sorry

        -- the composition is measurable
        · unfold c
          have F2Meas : Measurable F2 := by
            let lDMeas := leastDiffer_measurable
            measurability
          have F1Meas : Measurable F1 := by
            sorry
          measurability

      -- the other case of LN
      · exfalso
        have : Uncountable (ℕ → Bool) := nat_bool_uncountable
        have : Countable {y | (x, y) ∈ ordEdgeSet G} := lcbG.Ctbl _
        exact not_injective_uncountable_countable g gInj


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
    have GtoH_prop : ∀ p : X × X, G.Adj p.1 p.2 → H.Adj (isoC p.1) (isoC p.2) := by
      intro p h
      change (SimpleGraph.map isoC.toEmbedding G).Adj (isoC.toEmbedding p.1) (isoC.toEmbedding p.2)
      rw [SimpleGraph.map_adj]
      simp [h]
    let GtoH : ordEdgeSet G → ordEdgeSet H := fun (x : ordEdgeSet G) =>
      ⟨(isoC.toEmbedding x.1.1 , isoC.toEmbedding x.1.2), GtoH_prop x.1 x.2⟩
    let cG : ordEdgeSet G → ℕ := cH ∘ GtoH
    rcases hcH with ⟨h1, h2⟩
    · use cG
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro p q hpq
        rcases hpq with ⟨com , notsame⟩
        rcases com with case1 | case2 | case3 | case4
        all_goals {
          unfold cG
          simp only [Function.comp_apply, ne_eq]
          unfold GtoH
          apply h1.1
          grind
        }
        --
      · intro p q hpq
        unfold cG
        simp only [Function.comp_apply]
        unfold GtoH
        apply h1.2
        grind
      · unfold cG
        have h3 : Measurable GtoH := by measurability
        apply Measurable.fun_comp h2 h3



/- Feldman-Moore for CBERs: Suppose that E is a CBER on std Borel X, then there is
    a countable group Γ and a Borel action Γ → X whose orbit equivalence relation is E,
    i.e. x E y iff ∃ γ ∈ Γ (γ * x = y).
-/
open Classical in
theorem FeldmanMoore {X : Type*} (hNotCtbl : ¬Countable X) [MeasX : MeasurableSpace X]
    [stdborelX : StandardBorelSpace X] {E : X → X → Prop} (cberE : cBer E) :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : MeasurableSpace G) (_ : MulAction G X),
    BorelSpace G ∧ @cdGroup G _ _ ∧ MeasurableSMul₂ G X
    ∧ MulAction.orbitRel G X = E := by
  let graph := SimpleGraph.fromEdgeSet {x : Sym2 X | ∃ x1 x2 : x , x1 ≠ x2 ∧ E x1 x2}
  rcases cberE with ⟨h1, h2, h3⟩
  have lcbG : lcBGraph graph := by
    constructor
    · constructor
      unfold ordEdgeSet
      have : {p : X × X| graph.Adj p.1 p.2} = {p : X × X | E p.1 p.2} \ Set.diagonal X := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨hx1, hx2⟩
          simp only [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_diagonal_iff]
          constructor
          · simp only [Sym2.toRel_prop, Set.mem_setOf_eq] at hx1
            rcases hx1 with ⟨x1, ⟨x2, x3⟩⟩
            have in1 : x.1 = x1 ∨ x.1 = x2 := by grind
            have in2 : x.2 = x1 ∨ x.2 = x2 := by grind
            rcases in1 with eq11 | eq12
            · rcases in2 with  eq21 | eq22
              · grind
              · grind
            · rcases in2 with  eq21 | eq22
              · apply h2.symm
                grind
              · grind
          · apply hx2
        · intro hx
          rcases hx with ⟨hx1, hx2⟩
          simp at hx1
          simp only [Set.mem_diagonal_iff] at hx2
          unfold graph
          simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq]
          simp only [ne_eq, Subtype.exists, Sym2.mem_iff, exists_and_right, Subtype.mk.injEq,
            exists_prop, exists_eq_or_imp, ↓existsAndEq, true_and]
          constructor
          · constructor
            use x.2
            grind
          · exact hx2
      rw [this]
      apply MeasurableSet.diff
      · apply h1.Meas
      · have := stdborelX.instMeasurableEq
        apply this.measurableSet_diagonal
    · sorry
    · apply stdborelX
  have h := FeldmanMooreEdgeColoring_uncountable hNotCtbl lcbG
  rcases h with ⟨c, measc⟩
  let classes : ℕ → Set X := fun n => {x : X | ∃ e : ordEdgeSet graph, c e = n ∧ x = e.1.1}
  let invols : ℕ → X → X := fun n x => if x ∈ classes n ∧
    (∃ y : X , graph.Adj x y ∧ (c ⟨(x,y) , ?_⟩ = n)) then sorry
    else x
  swap
  · sorry
  have is_invol : ∀ n : ℕ , Function.Involutive (invols n) := by
    intro n x
    unfold invols
    sorry
  let G := Monoid.CoprodI fun n : ℕ => Multiplicative (ZMod 2)
  let topG : TopologicalSpace G := ⊥
  have disctopG: DiscreteTopology G := by
    exact discreteTopology_iff_forall_isOpen.mpr fun s ↦ trivial
  have discspaceG : discreteSpace G := by
    constructor
    apply disctopG
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
  let measG : MeasurableSpace G := ⊥
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
  have (n : ℕ) (x : X) : (Monoid.CoprodI.of (i := n) (Multiplicative.ofAdd 1) : G) • x = invols n x
    := by rfl
  use G, Monoid.CoprodI.instGroup fun n ↦ Multiplicative (ZMod 2), topG, measG, GactX
  constructor
  · have discmeasG : DiscreteMeasurableSpace G := by
      refine { forall_measurableSet := ?_ }
      intro s
      sorry
    sorry
  constructor
  · constructor
    · apply ctblG
    · apply discgroupG
  constructor
  · sorry

  sorry

end FeldmanMoore
