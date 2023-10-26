import Argyle.Logic.InterpretedNet
import Argyle.Logic.InhibitionNet
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
import Mathlib.Tactic.Contrapose

import Argyle.Logic.Syntax
open Syntax

/-══════════════════════════════════════════════════════════════════
  Building InterpretedNets from PrefModels
══════════════════════════════════════════════════════════════════-/
-- In this section, I'm implementing Hannes Leitgeb's construction
-- for completeness, following his paper
--     "Nonmonotonic reasoning by inhibition nets" (2001)

-- Suprisingly, not included in the standard library!
-- We simply 'insert' a new element x into a relation R,
-- along with 'Extens' which specifies how to extend R.
def Rel.insert (R : Rel World World) (x : World) (Extens : World → Prop) : Rel World World :=
  sorry
  -- fun m n =>
  --   if m = x then
  --     Extens n
  --   else
  --     R m n

def Rel.toList (R : Rel World World) : List (World × World) :=
  sorry

-- For any w ∈ M.worlds, we index its predecessors u ≼ w as a list
--     [u₁, u₂, ..., uₖ]
-- This ordering is arbitrary, but the important thing is that it
-- is *fixed* once and for all (so that we can reason about the indices).
def PrefModel.preds (M : PrefModel World) (w : World) : List World :=
  sorry

--------------------------------------------------------------------
theorem preds_index {M : PrefModel World} {u v : World} :
  M.Pref u v → ∃ i, u = ((M.preds v).get i) :=
--------------------------------------------------------------------
  sorry

-- This is the first part of the construction,
--    PrefModel --> Inhibition Net
-- See pages 186, 187 of the (2001) paper.
def PrefModel.toInhibitionNet (M : PrefModel World) : InhibitionNet World :=
  let bias := sorry
  -- let bias := (M.worlds.max' M.nonempty) + 1

  -- Edge is just the edges of the PrefModel, but with x, y swapped.
  -- Excit follows M.Pref, but
  -- we extend it so that bias ⟶ n for all nonminimal n.
{ Edge := M.Edge.swap
  Excit := M.Pref.insert bias (fun n => n ∉ M.best M.worlds.elems)
  Inhib := sorry
  proposition_map := fun p => { w | M.proposition_eval p w }

  nodes := M.worlds
  bias := bias
  acyclic := by
    -- Follows from the fact that the PrefModel is reflexive, transitive,
    -- and antisymmetric, but we have to work a bit for it.
    simp only [Acyclic]
    apply by_contradiction
    intro h
    push_neg at h
    conv at h => enter [1, x]; rw [not_isEmpty_iff]; rw [Rel.swap_path]

    match h with
    | ⟨w, hw⟩ => sorry
  connected := Rel.swap_connected M.edges_connected

  excit_edge := sorry
  inhib_excit := sorry
}

-- This is the second part of the construction,
--    Inhibition Net --> Interpreted ANN
-- See page 193 of the (2001) paper.
noncomputable
def InhibitionNet.toNet (N : InhibitionNet Node) : InterpretedNet Node := {
  net := {
    graph := {
      Edge := N.Edge
      Weight := sorry
      nodes := N.nodes
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

    bias := N.bias
    acyclic := N.acyclic
    connected := N.connected
  }

  proposition_map := N.proposition_map
}

-- We put the two parts of the construction together to get our Net!
noncomputable
def PrefModel.toNet (M : PrefModel World) : InterpretedNet World :=
  (M.toInhibitionNet).toNet

--------------------------------------------------------------------
lemma reachable_toNet {M : PrefModel World} {S : Set World} {w : World} :
  w ∈ reachable (M.toNet.net) S ↔ ∃ u, u ∈ S ∧ M.Edge w u  := by
--------------------------------------------------------------------
  apply Iff.intro
  case mp =>
    intro h₁
    match h₁ with
    | ⟨u, path, hu⟩ =>
      -- There's a path from u to w; so by induction on that path
      induction path
      case trivial => exact ⟨u, ⟨hu, M.edges_refl u⟩⟩
      case from_path x y path_ux edge_xy IH =>
        have h₂ : x ∈ reachable (PrefModel.toNet M).net S := by
          exact ⟨u, ⟨path_ux, hu⟩⟩
        have h₃ : M.Edge y x := by
          simp only [PrefModel.toNet, PrefModel.toInhibitionNet] at edge_xy
          simp only [InhibitionNet.toNet] at edge_xy
          simp only [Rel.swap] at edge_xy
          exact edge_xy

        -- By IH there exists a v ∈ S with M.Edge
        match IH h₂ with
        | ⟨v, hv⟩ =>
          exact ⟨v, ⟨hv.1, M.edges_trans h₃ hv.2⟩⟩

  case mpr =>
    intro h₁
    match h₁ with
    | ⟨u, hu⟩ =>
      exact ⟨u, ⟨Rel.Path.from_path Rel.Path.trivial hu.2, hu.1⟩⟩

--------------------------------------------------------------------
lemma propagate_toNet_helper₁ {M : PrefModel World} {S : Set World} :
  (M.toInhibitionNet).propagate S = (M.best (Sᶜ))ᶜ := by
--------------------------------------------------------------------
  apply Set.ext
  intro w
  simp only [InhibitionNet.propagate]
  apply Iff.intro

  ---------------------
  -- Forward Direction
  ---------------------
  case mp =>
    intro h₁
    simp only [Membership.mem, Set.Mem] at h₁

    -- By cases on propagation for InhibitionNet
    cases h₁
    case inl h₂ =>
      -- CASE: w ∈ S.  So w ∉ Sᶜ, so by [best_inclusion], w ∉ (best(Sᶜ))ᶜ.
      apply by_contradiction
      intro h
      simp at h
      have h₃ : w ∈ (Sᶜ) := best_inclusion h
      exact absurd h₂ h₃
    case inr h₂ =>
      cases h₂
      case inl h₃ =>
        -- CASE: w is the 'bias' node
        sorry
      case inr h₃ =>
        -- CASE: w is activated by some u
        -- (and there is no inhibitory edge that stops this)
        simp only [PrefModel.best]
        simp only [compl]
        rw [Set.mem_setOf]
        rw [Set.mem_setOf]
        rw [Set.mem_setOf]
        push_neg

        match h₃ with
        | ⟨u, hu⟩ =>
          push_neg at hu
          intro h₄

          -- We need to show that the node that excites w is not in S,
          -- and also w is not more preferable than it.
          have h₅ : u ∉ S := by
            sorry

          have h₆ : ¬PrefModel.Pref M w u := by
            sorry

          exact ⟨u, ⟨h₅, h₆⟩⟩

  ---------------------
  -- Backward Direction
  ---------------------
  case mpr =>
    intro h₁
    simp [Membership.mem, Set.Mem]
    simp only [PrefModel.best] at h₁
    simp only [compl] at h₁
    rw [Set.mem_setOf] at h₁
    rw [Set.mem_setOf] at h₁
    rw [Set.mem_setOf] at h₁
    push_neg at h₁

    -- Either w ∈ S (and so trivially w is active in the InhibitionNet),
    -- Or w ∉ S, and so ∃ u∉S such that w is *not* more preferred than u.
    by_cases w ∈ S
    case pos => exact Or.inl h
    case neg =>
      apply Or.inr
      apply Or.inr
      match h₁ h with
      | ⟨u, hu⟩ =>
        -- We need to show that u activates w, and there isn't any
        -- inhibitory edge to stop this.
        have h₂ : (PrefModel.toInhibitionNet M).Excit u w := by
          sorry

        have h₃ : ∀ b, ¬(PrefModel.toInhibitionNet M).Inhib b (u, w) := by
          sorry

        exact ⟨u, ⟨h₂, h₃⟩⟩

--------------------------------------------------------------------
lemma propagate_toNet_helper₂ {N : InhibitionNet Node} {S : Set Node} :
  propagate (N.toNet.net) S = N.propagate S := by
--------------------------------------------------------------------
  apply Set.ext
  intro w
  simp only [InhibitionNet.propagate, Membership.mem, Set.Mem]

  -- We will want to do induction on the layers of the net
  -- (to split up the ANN propagation)
  sorry

--------------------------------------------------------------------
lemma propagate_toNet {M : PrefModel World} {S : Set World} (w : World) :
  propagate (M.toNet.net) S = (M.best (Sᶜ))ᶜ := by
--------------------------------------------------------------------
  simp only [PrefModel.toNet]
  rw [propagate_toNet_helper₂]
  rw [propagate_toNet_helper₁]

-- This is the big theorem, which says that
-- PrefModel.toNet is a homomorphism.
-- This corresponds to the *COMPLETENESS* of the neural semantics
-- (in other words, this is the hard part!)
--------------------------------------------------------------------
theorem toNet_homomorphism {M : PrefModel World} {ϕ : Formula} {w : World} :
  (M.toNet; w ⊩ ϕ) ↔ (M; w ⊩ ϕ) := by
--------------------------------------------------------------------
  induction ϕ generalizing w

  case proposition p =>
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    simp [PrefModel.toNet, PrefModel.toInhibitionNet, InhibitionNet.toNet]

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
    conv => lhs; simp
    simp only [Neural.Base.satisfies, Neural.Base.interpret] at IH
    rw [not_iff_comm]
    rw [reachable_toNet]
    push_neg

    -- Rephrase our Inductive Hypothesis
    have IH : (⟦ϕ⟧_PrefModel.toNet M)ᶜ = {u | (M; u ⊩ ϕ)}ᶜ := by
      apply Set.ext
      intro w; simp
      rw [not_iff_not]
      exact IH

    -- Go in and apply IH to the right-hand side.  Then just swap the ∧!
    conv => rhs; enter [1, u, 1]; rw [IH]; simp
    conv => rhs; enter [1, u]; rw [and_comm]

  case Typ ϕ IH =>
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    rw [propagate_toNet w]
    simp

    -- Go in and apply IH to the right-hand side
    conv => rhs; enter [2, w, 2, u, 1, u]; rw [← IH]

--------------------------------------------------------------------
theorem toNet_models {M : PrefModel World} {ϕ : Formula} :
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
