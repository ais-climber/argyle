import Argyle.Net
import Argyle.Operators.Reachable
import Argyle.Operators.Propagate
import Mathlib.Data.Finset.Basic

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

-- Our models are "interpreted" neural networks, i.e. neural networks
-- along with a mapping from propositions to sets of neurons.
structure InterpretedNet where
  net : Net
  proposition_map : String → Set ℕ

-- We abbreviate the 'top' state of the net (the set of
-- all neurons)
def InterpretedNet.top (Net : InterpretedNet) : Set ℕ :=
  Net.net.graph.vertices.toFinset

-- Any neural network N has a uniquely determined interpretation
-- that maps each formula to a set of neurons.
def interpret (Net : InterpretedNet) : Formula → Set ℕ := fun
| pᵖ => Net.proposition_map p
| ⊤ => Net.top
| not ϕ => (interpret Net ϕ)ᶜ
| ϕ and ψ => (interpret Net ϕ) ∩ (interpret Net ψ)
| ⟨K⟩ ϕ => reachable Net.net (interpret Net ϕ)
| ⟨T⟩ ϕ => propagate Net.net (interpret Net ϕ)
notation:40 "⟦" ϕ:40 "⟧_" Net:40 => interpret Net ϕ
  
-- Relation for "net satisfies ϕ at point n"
def satisfies (Net : InterpretedNet) (ϕ : Formula) (n : ℕ) : Prop :=
  n ∈ (⟦ϕ⟧_Net) -- interpret Net ϕ
notation:35 net:40 "; " n:40 " ⊩ " ϕ:40 => satisfies net ϕ n

-- A net models a *formula* ϕ iff n ⊩ ϕ for *all* points n ∈ N
def models (Net : InterpretedNet) (ϕ : Formula) : Prop :=
  ∀ n, (Net; n ⊩ ϕ)

-- A net models a *list* Γ iff N ⊨ ϕ for all ϕ ∈ Γ 
def models_list (Net : InterpretedNet) (Γ : List Formula) : Prop :=
  ∀ ϕ ∈ Γ, models Net ϕ

-- Γ ⊨ ϕ holds if *for all* nets N, if N ⊨ Γ then N ⊨ ϕ.  
def entails (Γ : List Formula) (ϕ : Formula) : Prop :=
  ∀ (Net : InterpretedNet), models_list Net Γ → models Net ϕ 
notation:30 Γ:40 " ⊨ " ϕ:40 => entails Γ ϕ

-- Lemma: A net models ϕ iff ⟦ϕ⟧ = N.
-- Note that this lemma is automatically applied by Lean's
-- simplifier (we almost always want to reason about the term
-- on the RHS.)
--------------------------------------------------------------------
@[simp]
lemma models_interpret (Net : InterpretedNet) (ϕ : Formula) : 
  models Net ϕ ↔ (⟦ϕ⟧_Net) = Net.top := by
--------------------------------------------------------------------
  simp only [models]
  apply Iff.intro
  
  -- Forward direction; if ∀ n, (Net; n ⊩ ϕ) then ⟦ϕ⟧ = N  
  case mp => 
    intro h₁
    sorry

  -- Backwards direction; if ⟦ϕ⟧ = N then ∀ n, (Net; n ⊩ ϕ)
  case mpr => 
    intro h₁ n
    simp only [satisfies]
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

-- Semantic statement of modus ponens.
-- (It's convenient to have it as a seperate lemma.)
--------------------------------------------------------------------
lemma models_modpon {Net : InterpretedNet} {ϕ ψ : Formula} :
    models Net ϕ
  → models Net (ϕ ⟶ ψ)
    ----------------
  → models Net ψ := by
--------------------------------------------------------------------
  -- rw [models_interpret, models_interpret, models_interpret]
  intro h₁ h₂
  simp [interpret] at h₂
  sorry

-- Semantic statement of and-introduction
--------------------------------------------------------------------
lemma models_andintro {Net : InterpretedNet} {ϕ ψ : Formula} :
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
lemma models_top {Net : InterpretedNet} :
    models Net ⊤ := by
--------------------------------------------------------------------
  simp [interpret]


--------------------------------------------------------------------
lemma models_conjunction {Net : InterpretedNet} (Γ : List Formula) :
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
  prove ϕ → ∀ (Net : InterpretedNet), models Net ϕ := by
--------------------------------------------------------------------
  intro ϕ h₁ net
  
  -- We case on each of our proof rules and axioms
  induction h₁
  -- Proof Rules
  case modpon ϕ ψ h₂ h₃ IH₂ IH₃ => exact models_modpon IH₂ IH₃
  case know_necess ϕ h IH => 
    simp
    simp at IH
    sorry
  case typ_necess ϕ h IH => 
    simp
    simp at IH
    sorry

  -- Propositional Axioms
  case prop_intro ϕ ψ => 
    simp [interpret]
    sorry
  case prop_distr ϕ ψ ρ => 
    simp
    sorry
  case contrapos ϕ ψ => 
    simp
    sorry

  -- Axioms for [K]
  case know_distr ϕ ψ => 
    simp
    sorry
  case know_refl ϕ => 
    simp
    sorry
  case know_trans ϕ => 
    simp
    sorry
  case know_grz ϕ => 
    simp
    sorry

  -- Axioms for [T]
  case typ_refl ϕ => 
    simp
    sorry
  case typ_trans ϕ => 
    simp
    sorry


-- Strong Soundness: If ϕ follows from Γ (by our proof rules),
-- then Γ entails ϕ (i.e. it holds in every neural net model).
--------------------------------------------------------------------
theorem strong_soundness : ∀ (Γ : List Formula) (ϕ : Formula),
  Γ ⊢ ϕ → Γ ⊨ ϕ := by
--------------------------------------------------------------------
  simp only [follows, entails, models_list]
  intro Γ ϕ h₁ Net h₂
  
  match h₁ with
  | ⟨Δ, hΔ⟩ => 
    -- We have ⋀ Δ and (⋀ Δ) ⟶ ϕ, so we can apply modus ponens.
    have h₃ : models Net (⋀ Δ) := by
      apply models_conjunction Δ
      intro ϕ hϕ
      exact h₂ ϕ (List.Sublist.subset hΔ.1 hϕ)

    have h₄ : models Net ((⋀ Δ) ⟶ ϕ) := soundness _ hΔ.2 _
    exact models_modpon h₃ h₄
  
