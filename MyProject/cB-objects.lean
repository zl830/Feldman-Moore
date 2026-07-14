/- This file is for defining cBer and countable Borel graphs. -/

import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card


variable {X : Type*} [MeasurableSpace X]


/- Defining cBer -/

structure measR (E : X → X → Prop) where
  Meas : MeasurableSet { p : X × X | E p.1 p.2 }

structure ctblER (E : X → X → Prop) extends Equivalence E where
  Ctbl : ∀ (x : X), { y : X | E y x }.Countable

structure cBer [StandardBorelSpace X] (E: X → X → Prop) extends measR E, ctblER E



/- Defining locally countable Borel graphs-/

structure measGraph (G : SimpleGraph X) where
  Meas : MeasurableSet { p : X × X | G.Adj p.1 p.2 }

structure lcGraph (G : SimpleGraph X) where
  Ctbl : ∀ (x : X), { y : X | G.Adj x y }.Countable

structure lfGraph (G : SimpleGraph X) where
  Finite : ∀ (x : X), ({ y : X | G.Adj x y }).Finite

structure lbGraph (n : ℕ) (G : SimpleGraph X) where
  Bounded : ∀ (x : X), ({ y : X | G.Adj x y }).ncard ≤ n

structure lcBGraph (G : SimpleGraph X) extends measGraph G, lcGraph G where
  stdBorel : StandardBorelSpace X



/- Defining Borel edge colouring-/

structure isEdgeCol {G S : Type*} (c : G → S) (G : SimpleGraph X) where
  disjointCols : ( ∀ (p q : G.edgeSet), p ≠ q ) → (c p) ≠ (c q)

structure isMeasEdgeCol {G S : Type*} [MeasurableSpace S] [MeasurableSpace G]
    (c : G → S) (G : SimpleGraph X) extends isEdgeCol c G where
  measCol : Measurable c
