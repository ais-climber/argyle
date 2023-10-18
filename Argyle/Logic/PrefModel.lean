import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.LibrarySearch

-- A 'PrefModel' is a preferential possible-worlds model, i.e.
-- a usual possible worlds model with a preference ordering ≼ on worlds.
-- (Think of this as a graph)
-- TODO: How do I enforce 'rel' and 'pref' to be over 'worlds'?
-- TODO: Should I use 'Rel' or 'Relation'?
structure PrefModel where
  worlds : Set ℕ
  edges : ℕ → ℕ → Prop
  pref : ℕ → ℕ → Prop 
  proposition_eval : String → ℕ → Prop

  -- Frame properties for preferential models
  edges_refl : Reflexive edges
  edges_trans : Transitive edges
  -- ...

  pref_refl : Reflexive pref
  pref_trans : Transitive pref
  -- ...

-- w ∈ best(A) iff w ∈ A and w is preferred over any other u ∈ A. 
def PrefModel.best (M : PrefModel) (A : Set ℕ) : Set ℕ :=
  fun w => w ∈ A ∧ (∀ u, u ∈ A → M.pref w u)  

--------------------------------------------------------------------
theorem best_inclusion {M : PrefModel} {A : Set ℕ} :
  M.best A ⊆ A := by
--------------------------------------------------------------------
  intro w h₁
  exact h₁.1

--------------------------------------------------------------------
theorem best_idempotent {M : PrefModel} {A : Set ℕ} :
  M.best (M.best A) = M.best A := by
--------------------------------------------------------------------
  apply Set.ext
  intro w
  apply Iff.intro

  case mp => exact fun h₁ => h₁.1
  
  case mpr => 
    intro h₁
    exact ⟨h₁, fun u h₂ => h₁.2 _ h₂.1⟩