import Argyle.Logic.InterpretedNet
import Argyle.Operators.Reachable
import Argyle.Operators.Propagate
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.LibrarySearch

import Argyle.Logic.Syntax
open Syntax

namespace Neural.Base

/-══════════════════════════════════════════════════════════════════
  Syntax
══════════════════════════════════════════════════════════════════-/

/-══════════════════════════════════════════════════════════════════
  Semantics
══════════════════════════════════════════════════════════════════-/

-- Any neural network N has a uniquely determined interpretation
-- that maps each formula to a set of neurons.
def interpret (Net : InterpretedNet Node) : Formula → Set Node := fun
| pᵖ => Net.proposition_map p
| ⊤ => Net.top
| not ϕ => (interpret Net ϕ)ᶜ
| ϕ and ψ => (interpret Net ϕ) ∩ (interpret Net ψ)
| [K] ϕ => (reachable Net.net ((interpret Net ϕ)ᶜ))ᶜ
| [T] ϕ => (propagate Net.net ((interpret Net ϕ)ᶜ))ᶜ
notation:40 "⟦" ϕ "⟧_" Net => interpret Net ϕ

-- I had to define [K] ϕ as the *dual* of Reachable
-- and [T] ϕ as the *dual* of Propagate.  So here I
-- will quickly check that
--    ⟨K⟩ ϕ is Reachable, and
--    ⟨T⟩ ϕ is Propagate
-- as intended.
--------------------------------------------------------------------
theorem interpret_diaKnow {Net : InterpretedNet Node} {ϕ : Formula} :
  (⟦⟨K⟩ ϕ⟧_Net) = reachable Net.net (⟦ϕ⟧_Net) := by
--------------------------------------------------------------------
  unfold Formula.diaKnow
  simp [interpret]

--------------------------------------------------------------------
theorem interpret_diaTyp {Net : InterpretedNet Node} {ϕ : Formula} :
  (⟦⟨T⟩ ϕ⟧_Net) = propagate Net.net (⟦ϕ⟧_Net) := by
--------------------------------------------------------------------
  unfold Formula.diaTyp
  simp [interpret]


-- Relation for "net satisfies ϕ at point n"
def satisfies (Net : InterpretedNet Node) (n : Node) (ϕ : Formula) : Prop :=
  n ∈ (⟦ϕ⟧_Net) -- interpret Net ϕ
notation:35 net "; " n " ⊩ " ϕ => satisfies net n ϕ

-- A net models a *formula* ϕ iff n ⊩ ϕ for *all* points n ∈ N
def models (Net : InterpretedNet Node) (ϕ : Formula) : Prop :=
  ∀ n, (Net; n ⊩ ϕ)

-- A net models a *list* Γ iff N ⊨ ϕ for all ϕ ∈ Γ
def models_list (Net : InterpretedNet Node) (Γ : List Formula) : Prop :=
  ∀ ϕ ∈ Γ, models Net ϕ

-- Γ ⊨ ϕ holds if *for all* nets N, if N ⊨ Γ then N ⊨ ϕ.
def entails (Γ : List Formula) (ϕ : Formula) : Prop :=
  ∀ {Node : Type} (Net : InterpretedNet Node),
    models_list Net Γ → models Net ϕ
notation:30 Γ:40 " ⊨ " ϕ:40 => entails Γ ϕ

-- Lemma: A net models ϕ iff ⟦ϕ⟧ = N.
-- Note that this lemma is automatically applied by Lean's
-- simplifier (we almost always want to reason about the term
-- on the RHS.)
--------------------------------------------------------------------
@[simp]
lemma models_interpret (Net : InterpretedNet Node) (ϕ : Formula) :
  models Net ϕ ↔ (⟦ϕ⟧_Net) = Net.top := by
--------------------------------------------------------------------
  simp only [models, satisfies, InterpretedNet.top]
  apply Iff.intro

  -- Forward direction; if ∀ n, (Net; n ⊩ ϕ) then ⟦ϕ⟧ = N
  case mp =>
    intro h₁
    exact Set.eq_univ_of_forall h₁

  -- Backwards direction; if ⟦ϕ⟧ = N then ∀ n, (Net; n ⊩ ϕ)
  case mpr =>
    intro h₁ n
    rw [Set.eq_univ_iff_forall] at h₁
    exact h₁ n

-- This lemma helps us break down the semantics for ⟦ϕ ⟶ ψ⟧:
--     ⟦ϕ ⟶ ψ⟧ = N   iff   ⟦ϕ⟧ ⊆ ⟦ψ⟧
--------------------------------------------------------------------
lemma interpret_implication {Net : InterpretedNet Node} {ϕ ψ : Formula} :
  ((⟦ϕ⟧_Net) ⊆ (⟦ψ⟧_Net)) ↔ (⟦ϕ ⟶ ψ⟧_Net) = Net.top := by
--------------------------------------------------------------------
  simp only [InterpretedNet.top]
  apply Iff.intro

  -- Forward direction
  case mp =>
    intro h₁
    simp [interpret]
    rw [← Set.subset_empty_iff]
    rw [← Set.inter_compl_self (⟦ψ⟧_Net)]
    exact Set.inter_subset_inter_left _ h₁

  -- Backwards direction
  case mpr =>
    intro h₁
    simp [interpret] at h₁
    -- rw [← Set.subset_empty_iff] at h₁

    -- We show ⟦ϕ⟧ ⊆ ⟦ψ⟧ by contradiction;
    -- If some n ∈ ⟦ϕ⟧ but n ∉ ⟦ψ⟧, then n ∈ ⟦ϕ⟧ ∩ ⟦ψ⟧ᶜ = ∅
    apply by_contradiction
    intro h
    rw [Set.not_subset] at h
    match h with
    | ⟨n, hn⟩ =>
      have h₂ : n ∈ (⟦ϕ⟧_Net) ∩ (⟦ψ⟧_Net)ᶜ := hn
      rw [h₁] at h₂
      exact absurd h₂ (Set.not_mem_empty n)

/-══════════════════════════════════════════════════════════════════
  Proof System
══════════════════════════════════════════════════════════════════-/

-- prove ϕ means ϕ is a tautology (we can prove ϕ from nothing).
-- i.e. ϕ either is an axiom, or follows from other tautologies
-- by our proof rules.
inductive prove : Formula → Prop where
-- Proof rules
| modpon {ϕ ψ} :
    prove ϕ
  → prove (ϕ ⟶ ψ)
    ----------------
  → prove ψ

| know_necess {ϕ} :
    prove ϕ
    ----------------
  → prove ([K] ϕ)

-- Note that we do *not* have a Typ-Necessitation rule!
-- This is because there is a bias node in our neural networks
-- that is *always active*, i.e.
--    Propagate(∅) = {bias}
-- whereas we would need
--    Propagate(∅) = ∅
-- in order for necessitation to be true.
-- TODO: Bake in this bias in Propagate.lean!

-- Propositional Axioms
| prop_self  {ϕ}     : prove (ϕ ⟶ ϕ)
| prop_intro {ϕ ψ}   : prove (ϕ ⟶ (ψ ⟶ ϕ))
| prop_distr {ϕ ψ ρ} : prove ((ϕ ⟶ (ψ ⟶ ρ)) ⟶ ((ϕ ⟶ ψ) ⟶ (ϕ ⟶ ρ)))
| contrapos  {ϕ ψ}   : prove ((not ϕ ⟶ not ψ) ⟶ (ψ ⟶ ϕ))

-- Axioms for [K]
| know_distr {ϕ ψ} : prove ([K] (ϕ ⟶ ψ) ⟶ ([K] ϕ ⟶ [K] ψ))
| know_refl  {ϕ}   : prove ([K] ϕ ⟶ ϕ)
| know_trans {ϕ}   : prove ([K] ϕ ⟶ [K]([K] ϕ))
-- | know_grz   {ϕ}   : prove ([K] ([K] (ϕ ⟶ [K]ϕ) ⟶ ϕ) ⟶ ϕ)
-- TODO: Temporarily removing grz because I'm not sure if it's sound

-- Axioms for [T]
| typ_refl   {ϕ} : prove ([T] ϕ ⟶ ϕ)
| typ_trans  {ϕ} : prove ([T] ϕ ⟶ [T]([T] ϕ))

-- ⋀ Γ takes a big conjunction of all the formulas in Γ.
-- (keep in mind that Γ is finite by construction!)
def conjunction : List Formula → Formula := fun
| [] => ⊤
| ϕ :: ϕs => ϕ and (conjunction ϕs)
prefix:40 "⋀ " => conjunction

-- Γ ⊢ ϕ holds if there is some sublist Δ ⊆ Γ with ⊢ ⋀ Δ ⟶ ϕ
-- (ϕ follows from some finite subset of formulas in Γ)
def follows (Γ : List Formula) (ϕ : Formula) : Prop :=
  ∃ Δ, List.Sublist Δ Γ ∧ (prove ((⋀ Δ) ⟶ ϕ))
notation:30 Γ:40 " ⊢ " ϕ:40 => follows Γ ϕ

/-══════════════════════════════════════════════════════════════════
  Soundness
══════════════════════════════════════════════════════════════════-/

-- Semantic statement of modus ponens.
-- (It's convenient to have it as a seperate lemma.)
--------------------------------------------------------------------
lemma models_modpon {Net : InterpretedNet Node} {ϕ ψ : Formula} :
    models Net ϕ
  → models Net (ϕ ⟶ ψ)
    ----------------
  → models Net ψ := by
--------------------------------------------------------------------
  intro h₁ h₂
  simp at *
  rw [← interpret_implication] at h₂
  simp only [InterpretedNet.top] at *
  rw [h₁] at h₂
  rw [← Set.univ_subset_iff]
  exact h₂

-- Semantic statement of and-introduction
--------------------------------------------------------------------
lemma models_andintro {Net : InterpretedNet Node} {ϕ ψ : Formula} :
    models Net ϕ
  → models Net ψ
    ----------------
  → models Net (ϕ and ψ) := by
--------------------------------------------------------------------
  intro h₁ h₂
  simp at h₁
  simp at h₂
  simp [interpret, h₁, h₂]

-- Every neural network models ⊤!
--------------------------------------------------------------------
lemma models_top {Net : InterpretedNet Node} :
    models Net ⊤ := by
--------------------------------------------------------------------
  simp [interpret]


--------------------------------------------------------------------
lemma models_conjunction {Net : InterpretedNet Node} (Γ : List Formula) :
  (∀ ϕ ∈ Γ, models Net ϕ) → models Net (⋀ Γ) := by
--------------------------------------------------------------------
  intro h₁

  -- By induction on the list of formulas
  induction Γ
  case nil => simp only [conjunction, models_top]
  case cons ψ ψs IH =>
    simp only [conjunction]

    have h₂ : ∀ (ϕ : Formula), ϕ ∈ ψs → models Net ϕ := by
      intro ϕ h₂
      exact h₁ _ (List.mem_cons_of_mem _ h₂)

    -- On the left, show ⊨ ψ.  On the right, show ⊨ ⋀ ψs.
    exact models_andintro (h₁ _ (List.mem_cons_self _ _)) (IH h₂)


-- Soundness: If we can prove ϕ from nothing (just our proof rules alone),
-- then ϕ holds in every neural network model.
--------------------------------------------------------------------
theorem soundness : ∀ (ϕ : Formula),
  prove ϕ → ∀ (Net : InterpretedNet Node), models Net ϕ := by
--------------------------------------------------------------------
  intro ϕ h₁ net

  -- We case on each of our proof rules and axioms
  induction h₁
  -- Proof Rules
  case modpon ϕ ψ _ _ IH₂ IH₃ => exact models_modpon IH₂ IH₃

  case know_necess ϕ h IH =>
    rw [models_interpret]
    rw [models_interpret] at IH
    simp only [interpret, InterpretedNet.top]
    simp only [InterpretedNet.top] at IH

    -- We substitute in ⟦ϕ⟧ = N
    rw [IH]
    simp
    exact reach_empty _

  -- Propositional Axioms
  -- Since Lean's simp includes boolean algebra on sets,
  -- these are straightforward.
  case prop_self ϕ =>
    rw [models_interpret]
    rw [← interpret_implication]

  case prop_intro ϕ ψ =>
    rw [models_interpret]
    rw [← interpret_implication]
    rw [← Set.compl_subset_compl]
    simp [interpret]

  case prop_distr ϕ ψ ρ =>
    rw [models_interpret]
    rw [← interpret_implication]
    simp [interpret]
    apply And.intro

    -- Show (⟦ϕ⟧ ∩ ⟦ψ⟧ᶜ)ᶜ ∩ (⟦ϕ⟧ ∩ ⟦ρ⟧ᶜ) ⊆ ⟦ϕ⟧
    apply by_contradiction
    intro h
    rw [Set.not_subset] at h
    match h with
    | ⟨n, hn⟩ => exact absurd hn.1.2.1 hn.2

    -- Show (⟦ϕ⟧ ∩ ⟦ψ⟧ᶜ)ᶜ ∩ (⟦ϕ⟧ ∩ ⟦ρ⟧ᶜ) ⊆ ⟦ψ⟧
    apply And.intro
    apply by_contradiction
    intro h
    rw [Set.not_subset] at h
    rw [Set.compl_inter] at h
    rw [compl_compl] at h
    match h with
    | ⟨n, hn⟩ =>
      -- Since n ∈ ⟦ϕ⟧ᶜ ∪ ⟦ψ⟧, either n ∈ ⟦ϕ⟧ᶜ or n ∈ ⟦ψ⟧.
      -- In either case we get a contradiction.
      cases hn.1.1
      case inl h₁ => exact absurd hn.1.2.1 h₁
      case inr h₁ => exact absurd h₁ hn.2

    -- Show (⟦ϕ⟧ ∩ ⟦ψ⟧ᶜ)ᶜ ∩ (⟦ϕ⟧ ∩ ⟦ρ⟧ᶜ) ⊆ ⟦ρ⟧ᶜ
    apply by_contradiction
    intro h
    rw [Set.not_subset] at h
    match h with
    | ⟨n, hn⟩ => exact absurd hn.1.2.2 hn.2

  case contrapos ϕ ψ =>
    rw [models_interpret]
    rw [← interpret_implication]
    simp [interpret]

  -- Axioms for [K]
  case know_distr ϕ ψ =>
    rw [models_interpret]
    rw [← interpret_implication]
    simp [interpret]
    conv => rhs; enter [n, 2, 1]; rw [← compl_compl (⟦ϕ⟧_net)]
    exact reach_inter _ _ _

  case know_refl ϕ =>
    rw [models_interpret]
    rw [← interpret_implication]
    simp [interpret]
    rw [← Set.compl_subset_compl]
    rw [compl_compl]
    exact reach_is_extens _ _

  case know_trans ϕ =>
    rw [models_interpret]
    rw [← interpret_implication]
    simp only [interpret]
    rw [← Set.compl_subset_compl]
    rw [compl_compl]
    rw [compl_compl]
    rw [← reach_is_idempotent _ _]

  -- TODO: Temporarily removing grz because I'm not sure if it's sound
  -- case know_grz ϕ =>
  --   rw [models_interpret]
  --   rw [← interpret_implication]
  --   simp [interpret]
  --   exact reach_grz _ _

  -- Axioms for [T]
  case typ_refl ϕ =>
    rw [models_interpret]
    rw [← interpret_implication]
    simp only [interpret]
    rw [← Set.compl_subset_compl]
    rw [compl_compl]
    exact propagate_is_extens _ _

  case typ_trans ϕ =>
    rw [models_interpret]
    rw [← interpret_implication]
    simp only [interpret]
    rw [← Set.compl_subset_compl]
    rw [compl_compl]
    rw [compl_compl]
    rw [← propagate_is_idempotent _ _]


-- Strong Soundness: If ϕ follows from Γ (by our proof rules),
-- then Γ entails ϕ (i.e. it holds in every neural net model).
--------------------------------------------------------------------
theorem strong_soundness : ∀ (Γ : List Formula) (ϕ : Formula),
  Γ ⊢ ϕ → Γ ⊨ ϕ := by
--------------------------------------------------------------------
  simp only [follows, entails, models_list]
  intro Γ ϕ h₁ Node Net h₂

  match h₁ with
  | ⟨Δ, hΔ⟩ =>
    -- We have ⋀ Δ and (⋀ Δ) ⟶ ϕ, so we can apply modus ponens.
    have h₃ : models Net (⋀ Δ) := by
      apply models_conjunction Δ
      intro ϕ hϕ
      exact h₂ ϕ (List.Sublist.subset hΔ.1 hϕ)

    have h₄ : models Net ((⋀ Δ) ⟶ ϕ) := soundness _ hΔ.2 _
    exact models_modpon h₃ h₄

end Neural.Base
