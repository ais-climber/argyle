import Argyle.Net
import Argyle.Operators.Reachable
import Argyle.Operators.Propagate
import Argyle.Operators.Hebb
import Argyle.Logic.NeuralBase
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.LibrarySearch

-- TODO: How can I just refer to 'InterpretedNet'?
-- open NeuralBase.InterpretedNet

namespace NeuralHebb

/-══════════════════════════════════════════════════════════════════
  Syntax
══════════════════════════════════════════════════════════════════-/

-- The Logic of Hebbian Learning extends our base language
-- with a dynamic formula ⟨ϕ⟩_Hebb ψ.  
-- NOTE: There's a lot of redundancy with Argyle.Logic.NeuralBase, 
--    but I believe that's unavoidable (we can't *just* inherit 
--    the static formulas -- we need to be able to apply static 
--    connectives to dynamic formulas!)
inductive Formula : Type where
-- Propositional logic
| proposition : String → Formula
| top : Formula
| not : Formula → Formula
| and : Formula → Formula → Formula

-- "Possibly knows" and "Possibly finds typical of" modalities
| diaKnow : Formula → Formula
| diaTyp : Formula → Formula

-- The Hebbian update operator
| hebbop : Formula → Formula → Formula

-- Formula Notation
postfix:max "ᵖ"     => Formula.proposition
notation    "⊤"     => Formula.top
notation:85 "⟨" ϕ "⟩_Hebb " ψ => Formula.hebbop ϕ ψ
prefix:85   "⟨K⟩ "  => Formula.diaKnow
prefix:85   "⟨T⟩ "  => Formula.diaTyp
prefix:75   "not "  => Formula.not
infixl:65   " and " => Formula.and

-- Abbreviations
def Formula.Know : Formula → Formula := fun ϕ => not ⟨K⟩ (not ϕ)
def Formula.Typ : Formula → Formula := fun ϕ => not ⟨T⟩ (not ϕ)
def Formula.or : Formula → Formula → Formula := fun ϕ ψ => (not ((not ϕ) and (not ψ)))
def Formula.implies : Formula → Formula → Formula := fun ϕ ψ => Formula.or (not ϕ) ψ
def Formula.iff : Formula → Formula → Formula := fun ϕ ψ => (implies ϕ ψ) and (implies ψ ϕ)

prefix:85   "[K] "  => Formula.Know
prefix:85   "[T] "  => Formula.Typ
infixl:60   " or " => Formula.or
infixl:57   " ⟶ " => Formula.implies
infixl:55   " ⟷ " => Formula.iff

-- An example, as a sanity check
#check (⟨"a"ᵖ and "b"ᵖ⟩_Hebb ([K] "a"ᵖ ⟶ "b"ᵖ and [T] "c"ᵖ)) ⟶ "a"ᵖ

end NeuralHebb

/-══════════════════════════════════════════════════════════════════
  Syntactic Extension
══════════════════════════════════════════════════════════════════-/
-- We provide the embedding from the base language to the dynamic one,
-- which allows us to later inherit rules from the static logic.

def NeuralBase.Formula.lift : NeuralBase.Formula → NeuralHebb.Formula := fun
| pᵖ => pᵖ
| ⊤ => ⊤
| not ϕ => not (NeuralBase.Formula.lift ϕ)
| ϕ and ψ => (NeuralBase.Formula.lift ϕ) and (NeuralBase.Formula.lift ψ)
| ⟨K⟩ ϕ => ⟨K⟩ (NeuralBase.Formula.lift ϕ)
| ⟨T⟩ ϕ => ⟨T⟩ (NeuralBase.Formula.lift ϕ)

-- An example of lifting a static formula to the dynamic language.
#check 
  let x : NeuralBase.Formula := [K] "a"ᵖ ⟶ "b"ᵖ and [T] "c"ᵖ
  x.lift

/-══════════════════════════════════════════════════════════════════
  Semantics
══════════════════════════════════════════════════════════════════-/
-- Everything is the same as in our base logic, but we extend the
-- interpretation function to interpret the ⟨ϕ⟩_Hebb operator. 

namespace NeuralHebb

-- The uniquely determined interpretation function.
-- ⟨ϕ⟩_Hebb ψ says "interpret ψ in a new, Hebb-updated net."
def interpret (Net : InterpretedNet) : Formula → Set ℕ := fun
| pᵖ => Net.proposition_map p
| ⊤ => Net.top
| not ϕ => (interpret Net ϕ)ᶜ
| ϕ and ψ => (interpret Net ϕ) ∩ (interpret Net ψ)
| ⟨K⟩ ϕ => reachable Net.net (interpret Net ϕ)
| ⟨T⟩ ϕ => propagate Net.net (interpret Net ϕ)
| ⟨ϕ⟩_Hebb ψ => 
  let UpdatedNet := { Net with 
    net := hebb_star Net.net (interpret Net ϕ) }
  interpret UpdatedNet ψ
notation:40 "⟦" ϕ "⟧_" Net => interpret Net ϕ

def satisfies (Net : InterpretedNet) (ϕ : Formula) (n : ℕ) : Prop :=
  n ∈ (⟦ϕ⟧_Net) -- interpret Net ϕ
notation:35 net "; " n " ⊩ " ϕ => satisfies net ϕ n

def models (Net : InterpretedNet) (ϕ : Formula) : Prop :=
  ∀ n, (Net; n ⊩ ϕ)

def models_list (Net : InterpretedNet) (Γ : List Formula) : Prop :=
  ∀ ϕ ∈ Γ, models Net ϕ

def entails (Γ : List Formula) (ϕ : Formula) : Prop :=
  ∀ (Net : InterpretedNet), models_list Net Γ → models Net ϕ 
notation:30 Γ:40 " ⊨ " ϕ:40 => entails Γ ϕ


-- These are the same two semantic lemmas that we have for
-- the base logic.

-- Lemma: A net models ϕ iff ⟦ϕ⟧ = N.
--------------------------------------------------------------------
@[simp]
lemma models_interpret (Net : InterpretedNet) (ϕ : Formula) : 
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

--------------------------------------------------------------------
lemma interpret_implication {Net : InterpretedNet} {ϕ ψ : Formula} :
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

-- The next two lemmas are new.

-- This lemma helps us break down the semantics for ⟦ϕ ⟷ ψ⟧:
--     ⟦ϕ ⟷ ψ⟧ = N   iff   ⟦ϕ⟧ = ⟦ψ⟧
--------------------------------------------------------------------
lemma interpret_iff {Net : InterpretedNet} {ϕ ψ : Formula} :
  ((⟦ϕ⟧_Net) = (⟦ψ⟧_Net)) ↔ (⟦ϕ ⟷ ψ⟧_Net) = Net.top := by
--------------------------------------------------------------------
  simp only [InterpretedNet.top]
  apply Iff.intro
  
  -- Forward direction
  case mp =>
    intro h₁
    simp [interpret]
    simp [h₁]
    
  case mpr =>
    intro h₁
    simp only [Formula.iff] at h₁
    rw [Set.Subset.antisymm_iff]
    rw [interpret_implication, InterpretedNet.top]
    rw [interpret_implication, InterpretedNet.top]

    unfold interpret at h₁
    rw [Set.eq_univ_iff_forall, Set.eq_univ_iff_forall]
    rw [Set.eq_univ_iff_forall] at h₁
    exact ⟨fun x => (h₁ x).1, fun x => (h₁ x).2⟩

-- This lemma bridges our base logic semantics with our dynamic
-- logic semantics.
--------------------------------------------------------------------
lemma models_lift (Net : InterpretedNet) (ϕ : NeuralBase.Formula) :
  NeuralBase.models Net ϕ ↔ models Net ϕ.lift := by
--------------------------------------------------------------------
  -- By induction on ϕ
  induction ϕ
  case proposition p =>
    simp only [NeuralBase.Formula.lift]
    simp only [models, satisfies, interpret]
    simp only [NeuralBase.models, NeuralBase.satisfies, NeuralBase.interpret]
  case top => 
    simp only [NeuralBase.Formula.lift]
    simp only [models, satisfies]
    simp only [NeuralBase.models, NeuralBase.satisfies]
    exact ⟨fun h x => h x, fun h x => h x⟩  
  case _ ϕ IH => 
    simp only [NeuralBase.Formula.lift]
    simp only [models, satisfies, interpret]
    simp only [NeuralBase.models, NeuralBase.satisfies, NeuralBase.interpret]
    simp only [models, satisfies, interpret] at IH
    simp only [NeuralBase.models, NeuralBase.satisfies, NeuralBase.interpret] at IH
    sorry
    -- This is getting away from me a bit...
  case _ ϕ ψ IH₁ IH₂ => 
    simp only [NeuralBase.Formula.lift]
    sorry
  case diaKnow ϕ IH => 
    simp only [NeuralBase.Formula.lift]
    simp [models, satisfies, interpret]
    simp [models, satisfies, interpret] at IH
    sorry
  case diaTyp ϕ IH => 
    simp only [NeuralBase.Formula.lift]
    sorry

/-══════════════════════════════════════════════════════════════════
  Proof System
══════════════════════════════════════════════════════════════════-/

-- prove ϕ means ϕ is a tautology; ϕ either is an axiom, 
-- or follows from other tautologies by our proof rules.
inductive prove : Formula → Prop where
-- We lift all base logic tautologies
| hebb_lift {ϕ : NeuralBase.Formula} :
    NeuralBase.prove ϕ
    ----------------
  → prove ϕ.lift

-- Reduction Axioms
| hebb_prop  {P p}   : 
  prove ((⟨P⟩_Hebb pᵖ) ⟷ pᵖ)

| hebb_not   {P ϕ}   : 
  prove ((⟨P⟩_Hebb not ϕ) ⟷ not (⟨P⟩_Hebb ϕ))

| hebb_and   {P ϕ ψ} : 
  prove ((⟨P⟩_Hebb ϕ and ψ) ⟷ ((⟨P⟩_Hebb ϕ) and (⟨P⟩_Hebb ψ)))

| hebb_know  {P ϕ}   : 
  prove ((⟨P⟩_Hebb ⟨K⟩ ϕ) ⟷ ⟨K⟩ (⟨P⟩_Hebb ϕ))

| hebb_typ   {P ϕ}   : 
  prove ((⟨P⟩_Hebb ⟨T⟩ ϕ) ⟷ 
    ⟨T⟩ ((⟨P⟩_Hebb ϕ) or (⟨T⟩ P and ⟨K⟩ (⟨T⟩ P and ⟨T⟩ ⟨P⟩_Hebb ϕ))))


def conjunction : List Formula → Formula := fun
| [] => ⊤
| ϕ :: ϕs => ϕ and (conjunction ϕs)
prefix:40 "⋀ " => conjunction

def follows (Γ : List Formula) (ϕ : Formula) : Prop :=
  ∃ Δ, List.Sublist Δ Γ ∧ (prove ((⋀ Δ) ⟶ ϕ))
notation:30 Γ:40 " ⊢ " ϕ:40 => follows Γ ϕ


/-══════════════════════════════════════════════════════════════════
  Soundness
══════════════════════════════════════════════════════════════════-/
-- We have the same lemmas we had before for the base logic.

-- Semantic statement of modus ponens.
-- (It's convenient to have it as a seperate lemma.)
--------------------------------------------------------------------
lemma models_modpon {Net : InterpretedNet} {ϕ ψ : Formula} :
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
  induction h₁
  
  -- We case on each of our proof rules and axioms
  case hebb_lift ϕ h => 
    rw [← models_lift _ _]
    exact NeuralBase.soundness _ h _

  -- Reduction Axioms
  case hebb_prop P p => 
    rw [models_interpret]
    rw [← interpret_iff]
    simp [interpret]
  
  case hebb_not P ϕ => 
    rw [models_interpret]
    rw [← interpret_iff]
    simp [interpret]
  
  case hebb_and P ϕ ψ => 
    rw [models_interpret]
    rw [← interpret_iff]
    simp [interpret]
  
  case hebb_know P ϕ => 
    rw [models_interpret]
    rw [← interpret_iff]
    simp [interpret]
    exact hebb_reach _ _
  
  case hebb_typ P ϕ => 
    rw [models_interpret]
    rw [← interpret_iff]
    simp only [interpret]
    rw [← Set.compl_union]
    rw [compl_compl]
    exact hebb_reduction _ _ _


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

end NeuralHebb

