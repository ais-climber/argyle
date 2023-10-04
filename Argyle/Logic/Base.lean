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
notation:85 "[K] " ϕ:86 => not ⟨K⟩ (not ϕ)
notation:85 "[T] " ϕ:86 => not ⟨T⟩ (not ϕ)
notation:65 ϕ:65 " or " ψ:66 => not ϕ and not ψ
notation:64 ϕ:64 " ⟶ " ψ:65 => (not ϕ) or ψ

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
notation:35 net:40 ", " n:40 " ⊩ " ϕ:40 => satisfies net ϕ n

-- A net models a *formula* ϕ iff n ⊩ ϕ for *all* points n ∈ N
def models (net : Net) (ϕ : Formula) : Prop :=
  ∀ n, (net, n ⊩ ϕ)

-- A net models a *list* Γ iff N ⊨ ϕ for all ϕ ∈ Γ 
def models_list (net : Net) (Γ : List Formula) : Prop :=
  Γ.All₂ (fun ϕ => models net ϕ)

-- Γ ⊨ ϕ holds if *for all* nets N, if N ⊨ Γ then N ⊨ ϕ.  
def entails (Γ : List Formula) (ϕ : Formula) : Prop :=
  ∀ (net : Net), models_list net Γ → models net ϕ 
notation:30 Γ:40 " ⊨ " ϕ:40 => entails Γ ϕ

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

-- Soundness: If ϕ follows from Γ (by our proof rules),
-- then Γ entails ϕ (i.e. it holds in every neural net model).
--------------------------------------------------------------------
theorem soundness : ∀ (Γ : List Formula) (ϕ : Formula),
  Γ ⊨ ϕ → Γ ⊢ ϕ := by
--------------------------------------------------------------------
  -- induction ϕ
  sorry

-- We really want to prove *strong soundness*:
-- Γ ⊢ ϕ  implies  Γ ⊨ ϕ.
-- I haven't defined either of these things!
-- 
-- Right now I can only express *weak soundness*:
--   ⊢ ϕ  implies  ⊨ ϕ

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
