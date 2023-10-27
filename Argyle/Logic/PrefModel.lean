import Argyle.Helpers
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rel
import Mathlib.Tactic.LibrarySearch

-- Rel.best defines the ≼-minimal elements with respect
-- to some ordering R.  (We're going to use it for the
-- model's preference relation.)
-- a ∈ best(A) iff a ∈ A and a is ≼-minimal.
def Rel.best (R : Rel α α) (A : Set α) : Set α :=
  { w | w ∈ A ∧ (∀ u, u ∈ A → R w u) }

--------------------------------------------------------------------
theorem best_inclusion {R : Rel α α} {A : Set α} :
  R.best A ⊆ A := by
--------------------------------------------------------------------
  intro w h₁
  exact h₁.1

--------------------------------------------------------------------
theorem best_idempotent {R : Rel α α} {A : Set α} :
  R.best (R.best A) = R.best A := by
--------------------------------------------------------------------
  apply Set.ext
  intro w
  apply Iff.intro

  case mp => exact fun h₁ => h₁.1

  case mpr =>
    intro h₁
    exact ⟨h₁, fun u h₂ => h₁.2 _ h₂.1⟩

--------------------------------------------------------------------
theorem not_best_iff {R : Rel α α} {A : Set α} {w : α} :
  w ∉ R.best A ↔ (w ∉ A ∨ ∃ u, u ∈ A ∧ ¬ (R w u)) := by
--------------------------------------------------------------------
  simp only [Rel.best]
  simp only [compl]
  rw [Set.mem_setOf]
  rw [not_and_or]
  push_neg
  simp

-- Smoothness condition on a relation R
-- (corresponds to loop-cumulativity in a conditional logic)
def Smoothness (R : Rel α α) : Prop := ∀ (S : Set α) (u : α),
  u ∈ (R.best S) ∨ ∃ v, (R v u ∧ v ∈ (R.best S))

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
  worlds_nonempty : Nonempty World

  -- Frame properties for preferential models
  edges_refl : Reflexive Edge
  edges_trans : Transitive Edge
  edges_connected : Connected Edge
  -- ...

  pref_irrefl : Irreflexive Pref
  pref_trans : Transitive Pref
  pref_smooth : Smoothness Pref
  -- ...

  pref_edges : ∀ m n, Pref m n → Edge n m

  instance node_decidable : Decidable World := sorry

-- If we know u ≼ v, then we can't have v ≼ u.
-- This follows from irreflexivity and transitivity of Pref.
--------------------------------------------------------------------
theorem PrefModel.not_pref_of_pref {M : PrefModel World} {u v : World} :
  M.Pref u v → ¬ M.Pref v u := by
--------------------------------------------------------------------
  intro h₁
  apply by_contradiction
  intro h; simp at h

  have h₂ : M.Pref u u := M.pref_trans h₁ h
  exact absurd h₂ (M.pref_irrefl u)

-- There is some "least preferred" element of M, i.e. some w s.t.
-- ∀ u, u ≼ w.  This is what we will take to be our 'bias' element.
-- Since ≼ isn't a linear order, this upper bound might not be unique!
--
-- TODO: This *should* follow from irreflexivity and transitivity,
--   i.e. there are no cycles and so we should be able to find an end.
--------------------------------------------------------------------
theorem PrefModel.upper_bound {M : PrefModel World} :
  ∃ w, ∀ u, M.Pref u w := by
--------------------------------------------------------------------
  -- Rather than giving an explicit least preferred element, I argue
  -- by contradiction.
  apply by_contradiction
  intro h
  push_neg at h
  sorry
