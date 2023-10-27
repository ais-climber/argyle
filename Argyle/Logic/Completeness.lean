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
noncomputable
def PrefModel.toInhibitionNet (M : PrefModel World) : InhibitionNet World :=
  -- For the bias node, we just any arbitrary world that
  -- is less preferred than every other world (may not be unique).
  -- let bias := Classical.choose (Classical.exists_true_of_nonempty M.worlds_nonempty)
  let bias := Classical.choose M.upper_bound

  -- Edge is just the edges of the PrefModel, but with x, y swapped.
  -- Excit follows M.Pref, but we extend it so that bias ⟶ n for
  -- all nonminimal n.
{ Edge := M.Edge.swap
  Excit := fun u v =>
    if u = bias then
      v ∉ M.Pref.best M.worlds.elems
    else
      M.Pref u v
  Inhib := fun b ⟨u, v⟩ =>
    sorry
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

  -- If we have an excitation edge Excit m n,
  -- then we have an "ordinary" edge Edge m n.
  excit_edge := by
    intro m n h₁
    simp only [Rel.swap]
    by_cases m = bias

    -- Case: Excit m n, where m = bias
    -- (this means that n ∉ Best(N).)
    case pos =>
      rw [if_pos h] at h₁
      rw [h]
      sorry

    -- Case: Otherwise, we have Excit m n because m ≼ n.
    case neg =>
      rw [if_neg h] at h₁
      exact M.pref_edges _ _ h₁

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
  (M.toInhibitionNet).propagate S = (M.Pref.best (Sᶜ))ᶜ := by
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

      -- CASE: w is the 'bias' node
      case inl h₃ =>
        simp only [PrefModel.toInhibitionNet] at h₃
        rw [Set.mem_compl_iff]
        rw [not_best_iff]

        have h₄ : ∀ u, PrefModel.Pref M u w := by
          rw [h₃]
          exact Classical.choose_spec M.upper_bound
        by_cases w ∈ Sᶜ
        case neg => exact Or.inl h
        case pos => exact Or.inr ⟨w, ⟨h, M.pref_irrefl w⟩⟩

      -- CASE: w is activated by some u
      -- (and there is no inhibitory edge that stops this)
      case inr h₃ =>
        simp only [Rel.best]
        simp only [compl]
        rw [Set.mem_setOf]
        rw [Set.mem_setOf]
        rw [Set.mem_setOf]
        push_neg

        match h₃ with
        | ⟨u, hu⟩ =>
          intro h₄
          push_neg at hu
          simp only [PrefModel.toInhibitionNet] at hu

          -- This is the first use of the Smoothness condition of
          -- the PrefModel!  Either u ∈ Best(Sᶜ), or there's some
          -- more preferred v ∈ Best(Sᶜ).
          cases M.pref_smooth (Sᶜ) u

          -- CASE: u ∈ Best(Sᶜ).  So u ∈ Sᶜ, and u ≼ w (thus w ⋠ u).
          case inl h₄ =>
            have h₅ : u ∈ Sᶜ := best_inclusion h₄
            simp [Rel.best] at h₄
            exact ⟨u, ⟨h₅, M.not_pref_of_pref (h₄.2 w)⟩⟩

          -- CASE: Some other v ≼ u is v ∈ Best(Sᶜ).  So *this*
          --   v ∈ Sᶜ, and v ≼ w (thus w ⋠ v).
          case inr h₄ =>
            match h₄ with
            | ⟨v, hv⟩ =>
              have h₅ : v ∈ Sᶜ := best_inclusion hv.2
              simp [Rel.best] at hv
              exact ⟨v, ⟨h₅, M.not_pref_of_pref (hv.2.2 w)⟩⟩

  ---------------------
  -- Backward Direction
  ---------------------
  case mpr =>
    intro h₁
    simp [Membership.mem, Set.Mem]
    rw [Set.mem_compl_iff] at h₁
    rw [not_best_iff] at h₁
    simp at h₁

    -- Either w ∈ S (and so trivially w is active in the InhibitionNet),
    -- Or w ∉ S, and so ∃ u∉S such that w is *not* more preferred than u.
    by_cases w ∈ S
    case pos => exact Or.inl h
    case neg =>
      cases h₁
      case inl h₂ => exact absurd h₂ h
      case inr h₂ =>
        apply Or.inr
        apply Or.inr
        match h₂ with
        | ⟨u, hu⟩ =>
          -- This is where we use the Smoothness condition of
          -- the PrefModel!  Either u ∈ Best(Sᶜ), or there's some
          -- more preferred v ∈ Best(Sᶜ).
          cases M.pref_smooth (Sᶜ) u

          -- CASE: u ∈ Best(Sᶜ).  So u is more preferred than any other w ∈ Sᶜ.
          --   This means we have the edge from u ⟶ w, and that no other
          --   bias connection prevents this from activating.
          case inl h₃ =>
            -- CONSTRUCT EXCITATION EDGE
            have h₄ : (M.toInhibitionNet).Excit u w := by
              simp only [PrefModel.toInhibitionNet]

              -- Now we need to check whether u is the 'bias' node
              by_cases u = (PrefModel.toInhibitionNet M).bias
              case pos =>
                -- If u is the bias, we just need to show that w ∉ Best(W)
                simp only [PrefModel.toInhibitionNet] at h
                rw [if_pos h]
                rw [not_best_iff]
                exact Or.inr ⟨u, ⟨M.worlds.complete u, hu.2⟩⟩

              case neg =>
                -- Otherwise, we need to show that u ≼ w (u is more preferred than w)
                simp only [PrefModel.toInhibitionNet] at h
                rw [if_neg h]
                simp [Rel.best] at h₃
                exact h₃.2 w

            -- CONSTRUCT INHIBITION EDGE
            have h₅ : ∀ b, ¬(M.toInhibitionNet).Inhib b (u, w) := by
              intro b
              sorry

            exact ⟨u, ⟨h₄, h₅⟩⟩

          -- CASE: There's some better v ≼ u with v ∈ Best(Sᶜ).
          --   We match on this v; we show that there's an edge from v ⟶ w,
          --   and that no other bias connection prevents this from activating.
          case inr h₃ =>
            match h₃ with
            | ⟨v, hv⟩ =>
              -- CONSTRUCT EXCITATION EDGE
              have h₄ : (PrefModel.toInhibitionNet M).Excit v w := by
                simp only [PrefModel.toInhibitionNet]

                -- Now we need to check whether v is the 'bias' node
                by_cases v = (M.toInhibitionNet).bias
                case pos =>
                  -- If v is the bias, we just need to show that w ∉ Best(W)
                  -- This is exactly the same check as before.
                  simp only [PrefModel.toInhibitionNet] at h
                  rw [if_pos h]
                  rw [not_best_iff]
                  simp [Rel.best] at hv

                  -- NOTE: By irreflexivity and transitivity,
                  --   we have w ⋠ v  (since otherwise w ≼ v and v ≼ w)
                  have h₄ : ¬ M.Pref w v := by
                    apply by_contradiction
                    intro h; simp at h
                    exact absurd h (M.not_pref_of_pref (hv.2.2 w))

                  exact Or.inr ⟨v, ⟨M.worlds.complete v, h₄⟩⟩
                case neg =>
                  -- Otherwise, we need to show that v ≼ w (v is more preferred than w)
                  -- But this is true, because v ∈ Best(Sᶜ)!
                  simp only [PrefModel.toInhibitionNet] at h
                  rw [if_neg h]
                  simp [Rel.best] at hv
                  exact hv.2.2 w

              -- CONSTRUCT INHIBITION EDGE
              have h₅ : ∀ b, ¬(M.toInhibitionNet).Inhib b (v, w) := by
                intro b
                sorry

              exact ⟨v, ⟨h₄, h₅⟩⟩

--------------------------------------------------------------------
lemma propagate_toNet_helper₂ {N : InhibitionNet Node} {S : Set Node} :
  propagate (N.toNet.net) S = N.propagate S := by
--------------------------------------------------------------------
  apply Set.ext
  intro n
  simp only [InhibitionNet.propagate, Membership.mem, Set.Mem]
  simp only [propagate]

  -- By induction on the layer of the net containing n
  -- (to split up the ANN propagation)
  generalize hL : layer N.toNet.net n = L
  induction L

  ---------------------
  -- Base Step
  ---------------------
  case zero =>
    -- Most of these cases are trivial (either n ∈ S or n = bias),
    -- except for the last case which we show is impossible.
    simp only [propagate_acc]
    apply Iff.intro

    case mp =>
      intro h₁
      simp only [InhibitionNet.toNet] at h₁
      cases h₁
      case inl h₂ => exact Or.inl h₂
      case inr h₂ => exact Or.inr (Or.inl h₂)

    case mpr =>
      intro h₁
      simp only [InhibitionNet.toNet]
      cases h₁
      case inl h₂ => exact Or.inl h₂
      case inr h₂ =>
        cases h₂
        case inl h₃ => exact Or.inr h₃
        case inr h₃ =>
          -- This is the case that we will show is impossible.
          -- (n can't be at layer 0 *and* have some m ⟶ n)
          -- Right now the hypothesis gives us an m with Excit m n,
          -- so we'll match on that m.
          match h₃ with
          | ⟨m, hm⟩ =>
            have h₄ : (InhibitionNet.toNet N).net.graph.Edge m n := by
              simp only [InhibitionNet.toNet]
              exact N.excit_edge _ _ hm.1

            have h₅ : layer (InhibitionNet.toNet N).net m < 0 := by
              simp at hL
              rw [← hL]
              apply layer_preds
              rw [edge_iff_preds]
              exact h₄

            exact absurd h₅ (Nat.not_lt_zero (layer _ m))

  ---------------------
  -- Inductive Step
  ---------------------
  case succ L IH =>
    sorry

--------------------------------------------------------------------
lemma propagate_toNet {M : PrefModel World} {S : Set World} :
  propagate (M.toNet.net) S = (M.Pref.best (Sᶜ))ᶜ := by
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
    rw [propagate_toNet]
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
