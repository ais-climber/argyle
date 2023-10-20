import Argyle.Logic.InterpretedNet
import Argyle.Logic.PrefModel
import Argyle.Logic.Classical.Base
import Argyle.Logic.Neural.Base
import Argyle.Activation

import Argyle.Operators.Reachable
import Argyle.Operators.Propagate
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Logic.Relation
import Mathlib.Tactic.LibrarySearch

import Argyle.Logic.Syntax
open Syntax

/-══════════════════════════════════════════════════════════════════
  Building InterpretedNets from PrefModels
══════════════════════════════════════════════════════════════════-/
-- In this section, I'm implementing Hannes Leitgeb's construction
-- following his paper 
--     "Nonmonotonic reasoning by inhibition nets" (2001)
-- 
-- We first construct a special type of net called an
-- "inhibition net" (has no weights, but inhibitory synapses
-- control the flow of activation), and then we construct
-- a traditional ANN from the inhibition net.
-- 
-- An inhibitory edge connects a node to an excitatory edge, e.g.:
-- 
--         a --------> b
--               |
--               |
--         c ----⧸
-- 
-- Additionally, there are no weights or activation functions.
-- Excitatory edges always go through, unless some inhibitory
-- edge is currently preventing it from going through.

inductive Rel.Path (R : Rel ℕ ℕ) : ℕ → ℕ → Prop where
  | trivial {u : ℕ} :
      Path R u u
  | from_path {u v w : ℕ} : 
      Path R u v → R v w → Path R u w

-- Note that we don't allow reflexive edges at all.
def Rel.Acyclic (R : Rel ℕ ℕ) : Prop := ∀ (u v : ℕ),
  R.Path u v → ¬ R.Path v u

-- NOTE: As with InterpretedNets, we add a proposition mapping
-- as well.  We also have a 'bias' node, which occurs in *every*
-- activation.
structure InhibitionNet where
  nodes : Finset ℕ
  bias : ℕ
  excitatory_edges : Rel ℕ ℕ
  inhibitory_edges : Rel ℕ (ℕ × ℕ)
  
  -- The graph is nonempty, acyclic and fully connected.
  nonempty : nodes ≠ ∅
  acyclic : Rel.Acyclic excitatory_edges
  connected : Rel.Connected excitatory_edges
  proposition_map : String → Set ℕ


-- This is the first part of the construction,
--    PrefModel --> Inhibition Net
-- See pages 186, 187 of the (2001) paper.
def PrefModel.toInhibitionNet (M : PrefModel) : InhibitionNet := {
  nodes := M.worlds
  bias := (M.worlds.max' sorry) + 1
  excitatory_edges := fun m n => 
    if m = sorry then -- m = bias
      sorry -- TODO: just say 'n is not ≼-minimal
    else M.pref m n
  inhibitory_edges := sorry -- How should I index the nodes???

  nonempty := sorry
  acyclic := sorry
  connected := sorry

  proposition_map := fun p => { w | M.proposition_eval p w }
}

-- This is the second part of the construction,
--    Inhibition Net --> Interpreted ANN
-- See page 193 of the (2001) paper.
noncomputable
def InhibitionNet.toNet (N : InhibitionNet) : InterpretedNet := { 
  net := {
    graph := {
      vertices := N.nodes.toList
      edges := sorry
      weights := sorry

      edges_from_vertices_left := sorry
      edges_from_vertices_right := sorry
    }

    -- We just use a binary step activation function.
    -- The rate is somewhat arbitrary, since for the purposes
    -- of this construction we don't care about learning.
    -- So we just pick rate=1.
    activation := binary_step
    rate := 1
    rate_pos := by simp

    -- One possible threshold at which the activation function
    -- activates is T=1.
    binary := binary_step_is_binary
    activ_nondecr := binary_step_nondecr
    threshold := 1
    activ_thres := by simp

    nonempty := sorry
    acyclic := sorry
    connected := sorry
  }

  proposition_map := N.proposition_map
}

-- We put the two parts of the construction together to get our Net!
noncomputable
def PrefModel.toNet (M : PrefModel) : InterpretedNet :=
  (M.toInhibitionNet).toNet

-- TODO: I need to define the propagation of an Inhibition net first!
-- --------------------------------------------------------------------
-- lemma propagate_toInhibitionNet {M : PrefModel} {A : Set ℕ} : 
--   propagate (M.toNet.net) A = (M.best (Aᶜ))ᶜ :=
-- --------------------------------------------------------------------
--   sorry

-- --------------------------------------------------------------------
-- lemma propagate_toNet {M : PrefModel} {A : Set ℕ} : 
--   propagate (M.toNet.net) A = (M.best (Aᶜ))ᶜ :=
-- --------------------------------------------------------------------
--   sorry

-- TODO: How should I relate Reachability??


-- This is the big theorem, which says that
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
    sorry
  
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




/-══════════════════════════════════════════════════════════════════
  OLD: Soundness constructions that I decided I don't need
  right now.  They do not help with proving completeness
  for the neural semantics (and we've already shown soundness
  anyway, they're a bit redundant).
══════════════════════════════════════════════════════════════════-/
-- First, a couple of lemmas which establish soundness
-- for each of our frame properties (it's cleaner to separate
-- them from the main definition)
-- --------------------------------------------------------------------
-- lemma connected_toPrefModel {Net : InterpretedNet} :
--   Connected (Relation.ReflTransGen (Graph.hasEdge_Rel Net.net.graph)) := by
-- --------------------------------------------------------------------
--   intro x y
--   -- The model is connected because *Net* is connected!
--   cases (Net.net.connected x y)
--   case inl h₁ => 
--     apply Or.inl
--     apply Relation.ReflTransGen.single
--     exact Net.net.graph.hasEdgeRel_of_hasEdge x y h₁
--   case inr h₂ => 
--     cases h₂
--     case inl h₂₁ => 
--       apply Or.inr
--       apply Or.inl
--       apply Relation.ReflTransGen.single
--       exact Net.net.graph.hasEdgeRel_of_hasEdge y x h₂₁
--     case inr h₂₂ =>
--       apply Or.inr
--       apply Or.inr
--       sorry


-- def InterpretedNet.toPrefModel (Net : InterpretedNet) : PrefModel := {
--   -- worlds - just neurons in the neural net
--   -- edges  - the reflexive-transitive closure of edges in the neural net
--   worlds := Net.net.graph.get_vertices -- Net.net.graph.vertices  (make it a Set!)
--   edges := Relation.ReflTransGen Net.net.graph.hasEdge_Rel
--   pref := sorry
--   proposition_eval := fun p w => w ∈ Net.proposition_map p

--   -- "Soundness" direction for each of the frame properties
--   edges_refl := IsRefl.reflexive
--   edges_trans := Relation.transitive_reflTransGen
--   edges_connected := connected_toPrefModel

--   pref_refl := sorry
--   pref_trans := sorry
-- }

-- -- The following lemmas relate the Propagation in the 
-- -- InterpretedNet to the 'Best' function in the PrefModel.
-- -- These were first shown by Hannes Leitgeb (2001).
-- --------------------------------------------------------------------
-- lemma best_eq_propagate {Net : InterpretedNet} {A : Set ℕ} :
--   (Net.toPrefModel).best A = (propagate Net.net (Aᶜ))ᶜ :=
-- --------------------------------------------------------------------
--   sorry

-- -- This is the first big theorem, which says that
-- -- InterpretedNet.toPrefModel is a homomorphism,
-- -- i.e. preserves the satisfaction relation (and truth as well).
-- -- This corresponds to the *SOUNDNESS* of the neural semantics.
-- --------------------------------------------------------------------
-- lemma toPrefModel_homomorphism {Net : InterpretedNet} {ϕ : Formula} {n : ℕ} : 
--   (Net.toPrefModel; n ⊩ ϕ) ↔ (Net; n ⊩ ϕ) := by
-- --------------------------------------------------------------------
--   induction ϕ
--   case proposition p => 
--     simp only [Neural.Base.satisfies, Neural.Base.interpret]
--     simp only [Classical.Base.satisfies]
--     simp only [InterpretedNet.toPrefModel]
  
--   case top => 
--     simp only [Neural.Base.satisfies, Neural.Base.interpret]
--     simp only [InterpretedNet.top]
--     simp [Classical.Base.satisfies]
--     exact trivial
  
--   case _ ϕ IH => 
--     simp only [Neural.Base.satisfies, Neural.Base.interpret]
--     simp only [Classical.Base.satisfies]
--     rw [Set.mem_compl_iff]
--     rw [not_iff_not]
--     exact IH
  
--   case _ ϕ ψ IH₁ IH₂ => exact and_congr IH₁ IH₂
  
--   case Know ϕ IH => 
--     simp only [Neural.Base.satisfies, Neural.Base.interpret]
--     simp only [Classical.Base.satisfies]
--     sorry

  
--   case Typ ϕ IH => 
--     simp only [Neural.Base.satisfies, Neural.Base.interpret]
--     simp only [Classical.Base.satisfies]
--     rw [best_eq_propagate]
--     sorry

-- --------------------------------------------------------------------
-- theorem toPrefModel_models {Net : InterpretedNet} {ϕ : Formula} : 
--   Classical.Base.models (Net.toPrefModel) ϕ ↔ Neural.Base.models Net ϕ := by
-- --------------------------------------------------------------------
--   simp only [Classical.Base.models, Neural.Base.models]
--   apply Iff.intro
--   case mp => exact fun h₁ n => toPrefModel_homomorphism.mp (h₁ n)
--   case mpr => exact fun h₁ w => toPrefModel_homomorphism.mpr (h₁ w)