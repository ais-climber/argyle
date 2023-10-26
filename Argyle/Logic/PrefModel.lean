import Argyle.Helpers
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rel
import Mathlib.Tactic.LibrarySearch

-- A 'PrefModel' is a preferential possible-worlds model, i.e.
-- a usual possible worlds model with a preference ordering ≼ on worlds.
structure PrefModel (World : Type) where
  Edge : Rel World World
  Pref : Rel World World
  proposition_eval : String → World → Prop

  -- Whatever our worlds are, we need them to be provably
  -- finite and inhabited (nonempty)
  -- instance world_inhabited : Inhabited World := sorry
  worlds : Fintype World

  -- Frame properties for preferential models
  edges_refl : Reflexive Edge
  edges_trans : Transitive Edge
  edges_connected : Connected Edge
  -- ...

  pref_refl : Reflexive Pref
  pref_trans : Transitive Pref
  -- ...

-- w ∈ best(A) iff w ∈ A and w is ≼-minimal
-- (preferred over any other u ∈ A)
def PrefModel.best (M : PrefModel World) (A : Set World) : Set World :=
  { w | w ∈ A ∧ (∀ u, u ∈ A → M.Pref w u) }

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
