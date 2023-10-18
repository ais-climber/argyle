import Argyle.Logic.Syntax
import Argyle.Logic.PrefModel
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.LibrarySearch

import Argyle.Logic.Syntax
open Syntax

namespace Classical.Base

/-══════════════════════════════════════════════════════════════════
  Semantics
══════════════════════════════════════════════════════════════════-/

-- Relation for "net satisfies ϕ at point w"
-- This is the classical version that's mos
def satisfies (M : PrefModel) (w : ℕ) : Formula → Prop := fun
| pᵖ => M.proposition_eval p w
| ⊤ => (⊤ : Prop)
| not ϕ => ¬ (satisfies M w ϕ)
| ϕ and ψ => (satisfies M w ϕ) ∧ (satisfies M w ψ)
| [K] ϕ => ∀ u, M.edges w u → satisfies M u ϕ
| [T] ϕ => w ∈ M.best {u | satisfies M u ϕ}
notation:35 model "; " w " ⊩ " ϕ => satisfies model w ϕ

-- M models a *formula* ϕ iff w ⊩ ϕ for *all* points w ∈ M.worlds
def models (M : PrefModel) (ϕ : Formula) : Prop :=
  ∀ w, (M; w ⊩ ϕ)

-- M models a *list* Γ iff M ⊨ ϕ for all ϕ ∈ Γ 
def models_list (M : PrefModel) (Γ : List Formula) : Prop :=
  ∀ ϕ ∈ Γ, models M ϕ

-- Γ ⊨ ϕ holds if *for all* models M, if M ⊨ Γ then M ⊨ ϕ.  
def entails (Γ : List Formula) (ϕ : Formula) : Prop :=
  ∀ (M : PrefModel), models_list M Γ → models M ϕ 
notation:30 Γ:40 " ⊨ " ϕ:40 => entails Γ ϕ

-- This theorem says that the translation of conditionals ϕ ⟹ ψ
-- into our language coincides with the usual (KLM) definition
-- of conditionals:
--    ϕ ⟹ ψ   iff   every best ϕ-world is a ψ-world
--------------------------------------------------------------------
theorem conditional_def {M : PrefModel} {ϕ ψ : Formula} :
  models M (ϕ ⟹ ψ) ↔ 
    ∀ w, w ∈ M.best {u | satisfies M u ϕ} → satisfies M w ψ := by
--------------------------------------------------------------------
  unfold Formula.conditional
  simp [models, satisfies]


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
-- We also do not have the normal modal axiom for [T].
-- This means that [T] is not a normal modality.

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
lemma models_modpon {M : PrefModel} {ϕ ψ : Formula} :
    models M ϕ
  → models M (ϕ ⟶ ψ)
    ----------------
  → models M ψ := by
--------------------------------------------------------------------
  intro h₁ h₂
  simp [models, satisfies] at h₂
  intro w
  exact h₂ w (h₁ w)

-- Semantic statement of and-introduction
--------------------------------------------------------------------
lemma models_andintro {M : PrefModel} {ϕ ψ : Formula} :
    models M ϕ
  → models M ψ
    ----------------
  → models M (ϕ and ψ) := by
--------------------------------------------------------------------
  intro h₁ h₂
  simp [models, satisfies]
  intro w
  exact ⟨h₁ w, h₂ w⟩

-- Every M models ⊤!
--------------------------------------------------------------------
lemma models_top {M : PrefModel} :
    models M ⊤ := by
--------------------------------------------------------------------
  simp [models, satisfies]
  exact trivial

-- Same proof as in Neural.Base
--------------------------------------------------------------------
lemma models_conjunction {M : PrefModel} (Γ : List Formula) :
  (∀ ϕ ∈ Γ, models M ϕ) → models M (⋀ Γ) := by
--------------------------------------------------------------------
  intro h₁
  -- By induction on the list of formulas
  induction Γ
  case nil => simp only [conjunction, models_top]
  case cons ψ ψs IH => 
    simp only [conjunction]

    have h₂ : ∀ (ϕ : Formula), ϕ ∈ ψs → models M ϕ := by
      intro ϕ h₂
      exact h₁ _ (List.mem_cons_of_mem _ h₂)

    -- On the left, show ⊨ ψ.  On the right, show ⊨ ⋀ ψs.
    exact models_andintro (h₁ _ (List.mem_cons_self _ _)) (IH h₂)

-- Soundness: If we can prove ϕ from nothing (just our proof rules alone),
-- then ϕ holds in every neural network model.
--------------------------------------------------------------------
theorem soundness : ∀ (ϕ : Formula),
  prove ϕ → ∀ (M : PrefModel), models M ϕ := by
--------------------------------------------------------------------
  intro ϕ h₁ M
  
  -- We case on each of our proof rules and axioms
  induction h₁
  -- Proof Rules
  case modpon ϕ ψ _ _ IH₂ IH₃ => exact models_modpon IH₂ IH₃
  
  case know_necess ϕ h IH =>
    simp only [models, satisfies]
    exact fun w u _ => IH u

  -- Propositional Axioms
  -- Since Lean's simp includes propositional laws ('Prop'),
  -- these are straightforward.
  case prop_self ϕ => simp [models, satisfies]

  case prop_intro ϕ ψ => 
    simp [models, satisfies]
    exact fun w h₁ _ => h₁
    
  case prop_distr ϕ ψ ρ => 
    simp [models, satisfies]
    intro w h₁ h₂ h₃
    exact h₁ (h₃ h₂) h₂

  case contrapos ϕ ψ => 
    simp [models, satisfies]
    intro w h₁ h₂
    -- Contraposition can be done by contradiction
    apply by_contradiction
    exact fun h => h₁ h h₂
    
  -- Axioms for [K]
  case know_distr ϕ ψ => 
    simp [models, satisfies]
    intro w h₁ h₂ u h₃
    exact h₁ _ (h₂ _ h₃) h₃

  case know_refl ϕ => 
    simp [models, satisfies]
    intro w h₁
    exact h₁ w (M.edges_refl w)

  case know_trans ϕ => 
    simp [models, satisfies]
    intro w h₁ u h₂ v h₃
    exact h₁ _ (M.edges_trans h₂ h₃)

  -- Axioms for [T]
  case typ_refl ϕ => 
    simp [models, satisfies]
    intro w h₁
    have h₂ : w ∈ { u | M; u ⊩ ϕ } := best_inclusion h₁
    exact h₂
    
  case typ_trans ϕ => 
    simp [models, satisfies]
    intro w h₁
    rw [best_idempotent]
    exact h₁


-- Strong Soundness: If ϕ follows from Γ (by our proof rules),
-- then Γ entails ϕ (i.e. it holds in every neural net model).
--------------------------------------------------------------------
theorem strong_soundness : ∀ (Γ : List Formula) (ϕ : Formula),
  Γ ⊢ ϕ → Γ ⊨ ϕ := by
--------------------------------------------------------------------
  simp only [follows, entails, models_list]
  intro Γ ϕ h₁ M h₂
  
  match h₁ with
  | ⟨Δ, hΔ⟩ => 
    -- We have ⋀ Δ and (⋀ Δ) ⟶ ϕ, so we can apply modus ponens.
    have h₃ : models M (⋀ Δ) := by
      apply models_conjunction Δ
      intro ϕ hϕ
      exact h₂ ϕ (List.Sublist.subset hΔ.1 hϕ)

    have h₄ : models M ((⋀ Δ) ⟶ ϕ) := soundness _ hΔ.2 _
    exact models_modpon h₃ h₄

end Classical.Base