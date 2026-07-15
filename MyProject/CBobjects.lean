/- This file is for defining cBer and countable Borel graphs. -/

import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.Group.Basic


variable {X : Type*} [MeasurableSpace X]
set_option autoImplicit false

/- Defining cBer -/

structure measR (E : X → X → Prop) where
  Meas : MeasurableSet { p : X × X | E p.1 p.2 }

structure ctblER (E : X → X → Prop) extends Equivalence E where
  Ctbl : ∀ (x : X), { y : X | E y x }.Countable

structure cBer [StandardBorelSpace X] (E: X → X → Prop) extends measR E, ctblER E



/- Defining locally countable Borel graphs-/

/- ordEdgeSet is the ordered subset of X × X that is the edge set-/
def ordEdgeSet (G : SimpleGraph X) := { p : X × X | G.Adj p.1 p.2 }

structure measGraph (G : SimpleGraph X) where
  Meas : MeasurableSet (ordEdgeSet G)

structure lcGraph (G : SimpleGraph X) where
  Ctbl : ∀ (x : X), { y : X | G.Adj x y }.Countable

structure lfGraph (G : SimpleGraph X) where
  Finite : ∀ (x : X), ({ y : X | G.Adj x y }).Finite

structure lbGraph (n : ℕ) (G : SimpleGraph X) where
  Bounded : ∀ (x : X), ({ y : X | G.Adj x y }).ncard ≤ n

structure lcBGraph (G : SimpleGraph X) extends measGraph G, lcGraph G where
  stdBorel : StandardBorelSpace X



/- Defining Borel edge colouring-/

structure isEdgeCol {S : Type*} (G : SimpleGraph X) (c : ordEdgeSet G → S) where
  disjointCols : ( ∀ (p q : ordEdgeSet G), p ≠ q  → (c p) ≠ (c q) )

structure isMeasEdgeCol {S : Type*} [MeasurableSpace S] (G : SimpleGraph X) (c : ordEdgeSet G → S)
  extends isEdgeCol G c where
  measCol : Measurable c


/- Defining countable discrete groups -/

structure discreteSpace (S : Type*) [TopologicalSpace S] where
  discreteTop : DiscreteTopology S

structure discreteGroup (G : Type*) [TopologicalSpace G] [Group G] extends discreteSpace G where
  TopGroup : IsTopologicalGroup G

structure cdGroup {G : Type*} [Group G] [TopologicalSpace G] where
  ctbl : Countable G
  discrete : discreteGroup G

/- For Borel group actions : use MeasurableSMul₂-/
