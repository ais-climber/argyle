import Argyle.Logic.InterpretedNet
import Argyle.Logic.PrefModel
import Argyle.Logic.Classical.Base
import Argyle.Logic.Neural.Base

import Argyle.Operators.Reachable
import Argyle.Operators.Propagate
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.LibrarySearch

import Argyle.Logic.Syntax
open Syntax

/-══════════════════════════════════════════════════════════════════
  Translating between InterpretedNets and PrefModels
══════════════════════════════════════════════════════════════════-/

def InterpretedNet.toPrefModel (Net : InterpretedNet) : PrefModel := {
  worlds := sorry -- Net.net.graph.vertices  (make it a Set!)
  edges := sorry
  pref := sorry
  proposition_eval := fun p w => w ∈ Net.proposition_map p

  -- "Soundness" direction for each of the frame properties
  edges_refl := sorry
  edges_trans := sorry
  pref_refl := sorry
  pref_trans := sorry
}

def PrefModel.toNet (M : PrefModel) : InterpretedNet := { 
  net := {
    graph := {
      vertices := sorry
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
  Classical.Base.satisfies (Net.toPrefModel) n ϕ ↔ 
    Neural.Base.satisfies Net n ϕ := by
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
  Neural.Base.satisfies (M.toNet) w ϕ ↔ 
    Classical.Base.satisfies M w ϕ := by
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

