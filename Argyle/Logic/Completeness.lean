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
import Mathlib.Tactic.Contrapose

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

inductive Rel.Path (R : Rel World World) : World → World → Prop where
  | trivial {u : World} :
      Path R u u
  | from_path {u v w : World} :
      Path R u v → R v w → Path R u w

-- Note that we don't allow reflexive edges at all.
def Rel.Acyclic (R : Rel World World) : Prop := ∀ (u v : World),
  R.Path u v → ¬ R.Path v u

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

-- NOTE: As with InterpretedNets, we add a proposition mapping
-- as well.  We also have a 'bias' node, which occurs in *every*
-- activation.
-- There are three types of edges:
--   - Edge: Do nothing, act as a "skeleton" for excitatory edges.
--   - Excit: Excitatory edges that always go through, unless inhibited
--   - Inhib: Inhibitory edges that prevent excitatory edges from going through
structure InhibitionNet (Node : Type) where
  Edge : Rel Node Node -- NOTE: Skeleton edges do nothing; they just specify
                           -- where the excitatory edges can be
  Excit : Rel Node Node
  Inhib : Rel Node (Node × Node) -- need to be connected to excitatory_edges!!!
  proposition_map : String → Set Node

  -- There are finitely many nodes, and there is some node 'bias' ∈ Node.
  -- (bias is a node which shows up in the propagation of every signal.)
  nodes : Fintype Node
  bias : Node

  -- The graph is nonempty, acyclic and fully connected.
  acyclic : Rel.Acyclic Edge
  connected : Connected Edge

  -- The relationships between each of the edge types
  excit_edge : ∀ (m n : Node), Excit m n → Edge m n
  inhib_excit : ∀ (b m n : Node), Inhib b ⟨m, n⟩ → Excit m n

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

  nodes := sorry
  bias := bias
  acyclic := sorry
  connected := Rel.swap_connected M.edges_connected

  excit_edge := by
    sorry
    -- intro m n h₁ h₂
    -- simp only [Rel.insert] at h₂
    -- -- The if-statement here is false because m ∈ M.worlds!
    -- sorry
  inhib_excit := by
    sorry
    -- intro b m n h₁
    -- simp only [Rel.insert]
    -- sorry
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
      nodes := ⟨sorry, sorry⟩
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
      exact ⟨u, ⟨Graph.Path.from_path Graph.Path.trivial hu.2, hu.1⟩⟩

-- TODO: I need to define the propagation of an Inhibition net first!
--------------------------------------------------------------------
lemma propagate_toNet {M : PrefModel World} {S : Set World} (w : World) :
  propagate (M.toNet.net) S = (M.best (Sᶜ))ᶜ := by
--------------------------------------------------------------------
  sorry


-- This is the big theorem, which says that
-- PrefModel.toNet is a homomorphism.
-- This corresponds to the *COMPLETENESS* of the neural semantics
-- (in other words, this is the hard part!)
--------------------------------------------------------------------
lemma toNet_homomorphism {M : PrefModel World} {ϕ : Formula} {w : World} :
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
