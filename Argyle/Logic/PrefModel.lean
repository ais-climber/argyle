import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rel
import Mathlib.Tactic.LibrarySearch

-- A relation is fully connected iff all elements x y
-- are either related, or have exactly the same image
-- and preimage over R.
-- TODO: Synthesize the relations pov and the graph implementation!
def Rel.Connected {α : Type} (R : Rel α α) : Prop :=
  ∀ (x y), (R x y) ∨ (R y x)
    ∨ (R.image {x} = R.image {y}
        ∧ R.preimage {x} = R.preimage {y})

-- A 'PrefModel' is a preferential possible-worlds model, i.e.
-- a usual possible worlds model with a preference ordering ≼ on worlds.
-- (Think of this as a graph)
-- TODO: How do I enforce 'rel' and 'pref' to be over 'worlds'?
-- TODO: Should I use 'Rel' or 'Relation'?
structure PrefModel (World : Type) where
  worlds : Finset World
  Edge : Rel World World
  Pref : Rel World World
  proposition_eval : String → World → Prop

  -- Frame properties for preferential models
  nonempty : worlds.Nonempty
  edges_refl : Reflexive Edge
  edges_trans : Transitive Edge
  edges_connected : Rel.Connected Edge
  -- ...

  pref_refl : Reflexive Pref
  pref_trans : Transitive Pref
  -- ...

-- w ∈ best(A) iff w ∈ A and w is ≼-minimal
-- (preferred over any other u ∈ A)
def PrefModel.best (M : PrefModel World) (A : Set World) : Set World :=
  fun w => w ∈ A ∧ (∀ u, u ∈ A → M.Pref w u)

--------------------------------------------------------------------
theorem best_inclusion {M : PrefModel World} {A : Set World} :
  M.best A ⊆ A := by
--------------------------------------------------------------------
  intro w h₁
  exact h₁.1

--------------------------------------------------------------------
theorem best_idempotent {M : PrefModel World} {A : Set World} :
  M.best (M.best A) = M.best A := by
--------------------------------------------------------------------
  apply Set.ext
  intro w
  apply Iff.intro

  case mp => exact fun h₁ => h₁.1

  case mpr =>
    intro h₁
    exact ⟨h₁, fun u h₂ => h₁.2 _ h₂.1⟩
