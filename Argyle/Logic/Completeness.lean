import Argyle.Logic.InterpretedNet
import Argyle.Logic.PrefModel
import Argyle.Logic.Classical.Base
import Argyle.Logic.Neural.Base

import Argyle.Operators.Reachable
import Argyle.Operators.Propagate
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.LibrarySearch

import Argyle.Logic.Syntax
open Syntax

/-══════════════════════════════════════════════════════════════════
  Translating between InterpretedNets and PrefModels
══════════════════════════════════════════════════════════════════-/

-- First, a couple of lemmas which establish soundness
-- for each of our frame properties (it's cleaner to separate
-- them from the main definition)
--------------------------------------------------------------------
lemma connected_toPrefModel {Net : InterpretedNet} :
  Connected (Relation.ReflTransGen (Graph.hasEdge_Rel Net.net.graph)) := by
--------------------------------------------------------------------
  intro x y
  -- The model is connected because *Net* is connected!
  cases (Net.net.connected x y)
  case inl h₁ => 
    apply Or.inl
    apply Relation.ReflTransGen.single
    exact Net.net.graph.hasEdgeRel_of_hasEdge x y h₁
  case inr h₂ => 
    cases h₂
    case inl h₂₁ => 
      apply Or.inr
      apply Or.inl
      apply Relation.ReflTransGen.single
      exact Net.net.graph.hasEdgeRel_of_hasEdge y x h₂₁
    case inr h₂₂ =>
      apply Or.inr
      apply Or.inr
      sorry


def InterpretedNet.toPrefModel (Net : InterpretedNet) : PrefModel := {
  -- worlds - just neurons in the neural net
  -- edges  - the reflexive-transitive closure of edges in the neural net
  worlds := Net.net.graph.get_vertices -- Net.net.graph.vertices  (make it a Set!)
  edges := Relation.ReflTransGen Net.net.graph.hasEdge_Rel
  pref := sorry
  proposition_eval := fun p w => w ∈ Net.proposition_map p

  -- "Soundness" direction for each of the frame properties
  edges_refl := IsRefl.reflexive
  edges_trans := Relation.transitive_reflTransGen
  edges_connected := connected_toPrefModel

  pref_refl := sorry
  pref_trans := sorry
}

noncomputable
def PrefModel.toNet (M : PrefModel) : InterpretedNet := { 
  net := {
    graph := {
      vertices := M.worlds.toList
      edges := sorry
      weights := sorry

      edges_from_vertices_left := sorry
      edges_from_vertices_right := sorry
    }

    activation := sorry
    rate := sorry
    rate_pos := sorry

    binary := sorry
    activ_nondecr := sorry
    threshold := sorry
    activ_thres := sorry

    nonempty := sorry
    acyclic := sorry
    connected := sorry
  }

  proposition_map := fun p => { w | M.proposition_eval p w }
}

-- The following lemmas relate the Propagation in the 
-- InterpretedNet to the 'Best' function in the PrefModel.
-- These were first shown by Hannes Leitgeb (2001).
--------------------------------------------------------------------
lemma best_eq_propagate {Net : InterpretedNet} {A : Set ℕ} :
  (Net.toPrefModel).best A = (propagate Net.net (Aᶜ))ᶜ :=
--------------------------------------------------------------------
  sorry

--------------------------------------------------------------------
lemma propagate_eq_best {M : PrefModel} {A : Set ℕ} : 
  propagate (M.toNet.net) A = (M.best (Aᶜ))ᶜ :=
--------------------------------------------------------------------
  sorry

-- TODO: How should I relate Reachability??

-- This is the first big theorem, which says that
-- InterpretedNet.toPrefModel is a homomorphism,
-- i.e. preserves the satisfaction relation (and truth as well).
-- This corresponds to the *SOUNDNESS* of the neural semantics.
--------------------------------------------------------------------
lemma toPrefModel_homomorphism {Net : InterpretedNet} {ϕ : Formula} {n : ℕ} : 
  (Net.toPrefModel; n ⊩ ϕ) ↔ (Net; n ⊩ ϕ) := by
--------------------------------------------------------------------
  induction ϕ
  case proposition p => 
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    simp only [Classical.Base.satisfies]
    simp only [InterpretedNet.toPrefModel]
  
  case top => 
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    simp only [InterpretedNet.top]
    simp [Classical.Base.satisfies]
    exact trivial
  
  case _ ϕ IH => 
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    simp only [Classical.Base.satisfies]
    rw [Set.mem_compl_iff]
    rw [not_iff_not]
    exact IH
  
  case _ ϕ ψ IH₁ IH₂ => exact and_congr IH₁ IH₂
  
  case Know ϕ IH => 
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    simp only [Classical.Base.satisfies]
    sorry

  
  case Typ ϕ IH => 
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    simp only [Classical.Base.satisfies]
    rw [best_eq_propagate]
    sorry

--------------------------------------------------------------------
theorem toPrefModel_models {Net : InterpretedNet} {ϕ : Formula} : 
  Classical.Base.models (Net.toPrefModel) ϕ ↔ Neural.Base.models Net ϕ := by
--------------------------------------------------------------------
  simp only [Classical.Base.models, Neural.Base.models]
  apply Iff.intro
  case mp => exact fun h₁ n => toPrefModel_homomorphism.mp (h₁ n)
  case mpr => exact fun h₁ w => toPrefModel_homomorphism.mpr (h₁ w)


-- This is the other big theorem, which says that
-- PrefModel.toNet is a homomorphism.
-- This corresponds to the *COMPLETENESS* of the neural semantics
-- (in other words, this is the hard part!)
--------------------------------------------------------------------
lemma toNet_homomorphism {M : PrefModel} {ϕ : Formula} {w : ℕ} : 
  (M.toNet; w ⊩ ϕ) ↔ (M; w ⊩ ϕ) := by
--------------------------------------------------------------------
  induction ϕ
  
  case proposition p => 
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    simp [PrefModel.toNet]
  
  case top => 
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    simp [InterpretedNet.top]
    exact trivial
  
  case _ ϕ IH =>
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    rw [Set.mem_compl_iff]
    rw [not_iff_not]
    exact IH
  
  case _ ϕ ψ IH₁ IH₂ => exact and_congr IH₁ IH₂
  
  case Know ϕ IH => 
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    sorry
  
  case Typ ϕ IH => 
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    sorry

--------------------------------------------------------------------
theorem toNet_models {M : PrefModel} {ϕ : Formula} : 
  Neural.Base.models (M.toNet) ϕ ↔ Classical.Base.models M ϕ := by
--------------------------------------------------------------------
  simp only [Classical.Base.models, Neural.Base.models]
  apply Iff.intro
  case mp => exact fun h₁ n => toNet_homomorphism.mp (h₁ n)
  case mpr => exact fun h₁ w => toNet_homomorphism.mpr (h₁ w)

/-══════════════════════════════════════════════════════════════════
  Completeness for Classical Base Logic
══════════════════════════════════════════════════════════════════-/



/-══════════════════════════════════════════════════════════════════
  Completeness for Neural Base Logic
══════════════════════════════════════════════════════════════════-/
-- Since we already have model building & completeness for the 
-- base logic, and we can build an InterpretedNet from a PrefModel,
-- we get model building & completeness for free!



/-══════════════════════════════════════════════════════════════════
  Completeness for Neural Hebb Logic
══════════════════════════════════════════════════════════════════-/

