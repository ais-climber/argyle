import Argyle.Net
import Argyle.Operators.Reachable
import Argyle.Operators.Propagate

/-══════════════════════════════════════════════════════════════════
  Syntax
══════════════════════════════════════════════════════════════════-/

inductive Formula : Type where
-- Propositional logic
| proposition : String → Formula
| top : Formula
| not : Formula → Formula
| and : Formula → Formula → Formula

-- "Possibly knows" and "Possibly finds typical of" modalities
| diaKnow : Formula → Formula
| diaTyp : Formula → Formula

postfix:max "ᵖ"     => Formula.proposition
notation    "⊤"     => Formula.top
prefix:85   "⟨K⟩ "  => Formula.diaKnow
prefix:85   "⟨T⟩ "  => Formula.diaTyp
prefix:75   "not "  => Formula.not
infixl:65   " and " => Formula.and

-- Abbreviations
def Formula.Know : Formula → Formula := fun ϕ => not ⟨K⟩ (not ϕ)
def Formula.Typ : Formula → Formula := fun ϕ => not ⟨T⟩ (not ϕ)
def Formula.or : Formula → Formula → Formula := fun ϕ ψ => not ϕ and not ψ
def Formula.implies : Formula → Formula → Formula := fun ϕ ψ => or (not ϕ) ψ

prefix:85   "[K] "  => Formula.Know
prefix:85   "[T] "  => Formula.Typ
infixl:60   " or " => Formula.or
infixl:57   " ⟶ " => Formula.implies

-- Some sanity checks
#check [K] "a"ᵖ ⟶ "b"ᵖ and [T] "c"ᵖ


/-══════════════════════════════════════════════════════════════════
  Semantics
══════════════════════════════════════════════════════════════════-/

-- Any neural network N has a uniquely determined interpretation
-- that maps each formula to a set of neurons.
def interpret (net : Net) : Formula → Set ℕ := fun
| pᵖ => sorry
| ⊤ => sorry
| not ϕ => (interpret net ϕ)ᶜ
| ϕ and ψ => (interpret net ϕ) ∩ (interpret net ψ)
| ⟨K⟩ ϕ => reachable net (interpret net ϕ)
| ⟨T⟩ ϕ => propagate net (interpret net ϕ)

-- Relation for "net satisfies ϕ at point n"
def satisfies (net : Net) (ϕ : Formula) (n : ℕ) : Prop :=
  n ∈ interpret net ϕ
notation:35 net:40 "; " n:40 " ⊩ " ϕ:40 => satisfies net ϕ n

-- A net models a *formula* ϕ iff n ⊩ ϕ for *all* points n ∈ N
def models (net : Net) (ϕ : Formula) : Prop :=
  ∀ n, (net; n ⊩ ϕ)

-- A net models a *list* Γ iff N ⊨ ϕ for all ϕ ∈ Γ 
def models_list (net : Net) (Γ : List Formula) : Prop :=
  ∀ ϕ ∈ Γ, models net ϕ

  -- Γ.All₂ (fun ϕ => models net ϕ)
-- ∀ a ∈ l, p a

-- Γ ⊨ ϕ holds if *for all* nets N, if N ⊨ Γ then N ⊨ ϕ.  
def entails (Γ : List Formula) (ϕ : Formula) : Prop :=
  ∀ (net : Net), models_list net Γ → models net ϕ 
notation:30 Γ:40 " ⊨ " ϕ:40 => entails Γ ϕ

-- Lemma: A net models ϕ iff ⟦ϕ⟧ = N.
--------------------------------------------------------------------
lemma models_interpret (net : Net) (ϕ : Formula) : 
  models net ϕ ↔ interpret net ϕ = sorry := by
--------------------------------------------------------------------
  sorry

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

| typ_necess {ϕ} :
    prove ϕ
    ----------------
  → prove ([T] ϕ)

-- Propositional Axioms
| prop_intro {ϕ ψ}   : prove (ϕ ⟶ (ψ ⟶ ϕ))
| prop_distr {ϕ ψ ρ} : prove ((ϕ ⟶ (ψ ⟶ ρ)) ⟶ ((ϕ ⟶ ψ) ⟶ (ϕ ⟶ ρ)))
| contrapos  {ϕ ψ}   : prove ((not ϕ ⟶ not ψ) ⟶ (ψ ⟶ ϕ))

-- Axioms for [K]
| know_distr {ϕ ψ} : prove ([K] (ϕ ⟶ ψ) ⟶ ([K] ϕ ⟶ [K] ψ))
| know_refl  {ϕ}   : prove ([K] ϕ ⟶ ϕ)
| know_trans {ϕ}   : prove ([K] ϕ ⟶ [K]([K] ϕ))
| know_grz   {ϕ}   : prove ([K] ([K] (ϕ ⟶ [K]ϕ) ⟶ ϕ) ⟶ ϕ)

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

--------------------------------------------------------------------
lemma models_conjunction {net : Net} (Γ : List Formula) :
  (∀ ϕ ∈ Γ, models net ϕ) → models net (⋀ Γ) := by
--------------------------------------------------------------------
  intro h₁

  -- By induction on the list of formulas
  induction Γ
  case nil => sorry
  case cons ϕ ϕs IH => sorry

-- Semantic statement of modus ponens.
-- (It's convenient to have it as a seperate lemma.)
--------------------------------------------------------------------
lemma models_modpon {net : Net} {ϕ ψ : Formula} :
    models net ϕ
  → models net (ϕ ⟶ ψ)
    ----------------
  → models net ψ := by
--------------------------------------------------------------------
  sorry

-- Soundness: If we can prove ϕ from nothing (just our proof rules alone),
-- then ϕ holds in every neural network model.
--------------------------------------------------------------------
theorem soundness : ∀ (ϕ : Formula),
  prove ϕ → ∀ (net : Net), models net ϕ := by
--------------------------------------------------------------------
  intro ϕ h₁ net
  
  -- We case on each of our proof rules and axioms
  induction h₁
  -- Proof Rules
  case modpon ϕ ψ h₂ h₃ IH₂ IH₃ => exact models_modpon IH₂ IH₃
  case know_necess ϕ h IH => sorry
  case typ_necess ϕ h IH => sorry

  -- Propositional Axioms
  case prop_intro ϕ ψ => sorry
  case prop_distr ϕ ψ ρ => sorry
  case contrapos ϕ ψ => sorry

  -- Axioms for [K]
  case know_distr ϕ ψ => sorry
  case know_refl ϕ => sorry
  case know_trans ϕ => sorry
  case know_grz ϕ => sorry

  -- Axioms for [T]
  case typ_refl ϕ => sorry
  case typ_trans ϕ => sorry


-- Strong Soundness: If ϕ follows from Γ (by our proof rules),
-- then Γ entails ϕ (i.e. it holds in every neural net model).
--------------------------------------------------------------------
theorem strong_soundness : ∀ (Γ : List Formula) (ϕ : Formula),
  Γ ⊢ ϕ → Γ ⊨ ϕ := by
--------------------------------------------------------------------
  simp only [follows, entails, models_list]
  intro Γ ϕ h₁ net h₂
  
  match h₁ with
  | ⟨Δ, hΔ⟩ => 
    -- We have ⋀ Δ and (⋀ Δ) ⟶ ϕ, so we can apply modus ponens.
    have h₃ : models net (⋀ Δ) := by
      apply models_conjunction Δ
      intro ϕ hϕ
      exact h₂ ϕ (List.Sublist.subset hΔ.1 hϕ)

    have h₄ : models net ((⋀ Δ) ⟶ ϕ) := soundness _ hΔ.2 _
    exact models_modpon h₃ h₄
  

/-
soundness : ∀ (φ : Formula) → ⊢ φ → ⊨ φ

---------------------------------------
-- Propositional axioms
---------------------------------------
soundness (φ ⇒ (ψ ⇒ (φ ∧ ψ))) ∧-I M =
  {!   !}


---------------------------------------
-- MODUS PONENS
---------------------------------------
soundness ψ (modpon {φ} ⊢φ ⊢φ⇒ψ) = 
  let IH-φ = soundness φ ⊢φ in
  let IH-φ⇒ψ = soundness (φ ⇒ ψ) ⊢φ⇒ψ in
  λ M wₘ → IH-φ⇒ψ M wₘ (IH-φ M wₘ)

---------------------------------------
-- NECESSITATION
---------------------------------------
soundness ([ x , y ] φ) (necess ⊢φ) (⟨ η , T ⟩) wₘ = 
  let IH = soundness φ ⊢φ in
  ⟨ w⋆ , ⟨ y⋆ , 
    ⟨ refl , 
      ⟨ (IH (⟨ η , T ⟩) w⋆) , refl ⟩ ⟩ ⟩ ⟩
  where
    y⋆ = bool ⌊ T Data.Float.<? vsm.dot-prod wₘ ⟦ x ⟧ⱽ ⌋
    w⋆ = vsm.add wₘ (vsm.scalar-mult η (vsm.scalar-mult
          ((if ⟦ y ⟧ᴮ then 1.0 else 0.0) Data.Float.-
           (if ⌊ T Data.Float.<? vsm.dot-prod wₘ ⟦ x ⟧ⱽ ⌋ then 1.0 else 0.0))
          ⟦ x ⟧ⱽ))

---------------------------------------
-- EQUATIONAL
---------------------------------------
soundness (EQN E) (eqn ⊢ⱽE) = 
  λ M wₘ → vsm-soundness ⊢ⱽE

---------------------------------------
-- WEIGHTS UNIQUENESS
---------------------------------------
soundness (weights_ (vec w₁) ∧ weights_ (vec w₂) ⇒ EQN ((vec w₁) ≡ⱽ (vec w₂))) weights =
  λ M wₘ wₘ≡w₁×wₘ≡w₂ → vec-lift-lemma w₁ w₂ 
    (begin
      vec w₁      ≡⟨ sym (proj₁ wₘ≡w₁×wₘ≡w₂) ⟩
      vec wₘ      ≡⟨ proj₂ wₘ≡w₁×wₘ≡w₂ ⟩ 
      vec w₂
    ∎)
-/
