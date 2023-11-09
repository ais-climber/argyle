import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch

/-══════════════════════════════════════════════════════════════════
  Closure Language Syntax
══════════════════════════════════════════════════════════════════-/
namespace Closure

-- Language with □ and □∗
inductive Formula : Type where
| proposition : String → Formula
| top : Formula
| not : Formula → Formula
| and : Formula → Formula → Formula
| Oper : Formula → Formula
| Closure : Formula → Formula

postfix:max "ᵖ"     => Formula.proposition
notation    "⊤"     => Formula.top
prefix:85   "□ "  => Formula.Oper
prefix:85   "□∗ "  => Formula.Closure
prefix:75   "not "  => Formula.not
infixl:65   " and " => Formula.and

-- Abbreviations
def Formula.diaOper : Formula → Formula := fun ϕ => not □ (not ϕ)
def Formula.diaClosure : Formula → Formula := fun ϕ => not □∗ (not ϕ)
def Formula.or : Formula → Formula → Formula := fun ϕ ψ => (not ((not ϕ) and (not ψ)))
def Formula.implies : Formula → Formula → Formula := fun ϕ ψ => or (not ϕ) ψ
def Formula.iff : Formula → Formula → Formula := fun ϕ ψ => (implies ϕ ψ) and (implies ψ ϕ)

prefix:85   "◇ "  => Formula.diaOper
prefix:85   "◇∗ "  => Formula.diaClosure
infixl:60   " or " => Formula.or
infixl:57   " ⟶ " => Formula.implies
infixl:55   " ⟷ " => Formula.iff

end Closure

/-══════════════════════════════════════════════════════════════════
  Reduction Language Syntax
══════════════════════════════════════════════════════════════════-/
namespace Reduct

-- Language with □ and □⁻
inductive Formula : Type where
| proposition : String → Formula
| top : Formula
| not : Formula → Formula
| and : Formula → Formula → Formula
| Oper : Formula → Formula
| Reduct : Formula → Formula

postfix:max "ᵖ"     => Formula.proposition
notation    "⊤"     => Formula.top
prefix:85   "□ "  => Formula.Oper
prefix:85   "□⁻ "  => Formula.Reduct
prefix:75   "not "  => Formula.not
infixl:65   " and " => Formula.and

-- Abbreviations
def Formula.diaOper : Formula → Formula := fun ϕ => not □ (not ϕ)
def Formula.diaReduct : Formula → Formula := fun ϕ => not □⁻ (not ϕ)
def Formula.or : Formula → Formula → Formula := fun ϕ ψ => (not ((not ϕ) and (not ψ)))
def Formula.implies : Formula → Formula → Formula := fun ϕ ψ => Formula.or (not ϕ) ψ
def Formula.iff : Formula → Formula → Formula := fun ϕ ψ => (implies ϕ ψ) and (implies ψ ϕ)

prefix:85   "◇ "  => Formula.diaOper
prefix:85   "◇⁻ "  => Formula.diaReduct
infixl:60   " or " => Formula.or
infixl:57   " ⟶ " => Formula.implies
infixl:55   " ⟷ " => Formula.iff

end Reduct

/-══════════════════════════════════════════════════════════════════
  Semantics for the Closure
══════════════════════════════════════════════════════════════════-/
namespace Closure

structure Model (World : Type) where
  Edge : World → World → Prop
  proposition_eval : String → World → Prop

  -- Whatever our worlds are, we need them to be finite
  worlds : Fintype World

-- Relation for "net satisfies ϕ at point w"
-- This is the classical version that's mos
def satisfies (M : Model World) (w : World) : Formula → Prop := fun
| pᵖ => M.proposition_eval p w
| ⊤ => (⊤ : Prop)
| not ϕ => ¬ (satisfies M w ϕ)
| ϕ and ψ => (satisfies M w ϕ) ∧ (satisfies M w ψ)
| □ ϕ => ∀ u, M.Edge w u → satisfies M u ϕ
| □∗ ϕ => ∀ u, (Relation.ReflTransGen M.Edge) w u → satisfies M u ϕ
notation:35 model "; " w " ⊩ " ϕ => satisfies model w ϕ

-- M models a *formula* ϕ iff w ⊩ ϕ for *all* points w ∈ M.worlds
def models (M : Model World) (ϕ : Formula) : Prop :=
  ∀ (w : World), (M; w ⊩ ϕ)

-- ϕ is valid if it holds in all models
def valid (ϕ : Formula) : Prop :=
  ∀ {World : Type} (M : Model World), models M ϕ
notation:30 " ⊨ " ϕ:30 => valid ϕ

end Closure

/-══════════════════════════════════════════════════════════════════
  Semantics for the Reduction
══════════════════════════════════════════════════════════════════-/
def Relation.ReflTransReduction (R : α → α → Prop) : α → α → Prop :=
  sorry

namespace Reduct

structure Model (World : Type) where
  Edge : World → World → Prop
  proposition_eval : String → World → Prop

  -- Whatever our worlds are, we need them to be finite
  worlds : Fintype World

  -- Frame properties for preferential models
  refl : Reflexive Edge
  trans : Transitive Edge

-- Relation for "net satisfies ϕ at point w"
-- This is the classical version that's mos
def satisfies (M : Model World) (w : World) : Formula → Prop := fun
| pᵖ => M.proposition_eval p w
| ⊤ => (⊤ : Prop)
| not ϕ => ¬ (satisfies M w ϕ)
| ϕ and ψ => (satisfies M w ϕ) ∧ (satisfies M w ψ)
| □ ϕ => ∀ u, M.Edge w u → satisfies M u ϕ
| □⁻ ϕ => ∀ u, (Relation.ReflTransReduction M.Edge) w u → satisfies M u ϕ
notation:35 model "; " w " ⊩ " ϕ => satisfies model w ϕ

-- M models a *formula* ϕ iff w ⊩ ϕ for *all* points w ∈ M.worlds
def models (M : Model World) (ϕ : Formula) : Prop :=
  ∀ (w : World), (M; w ⊩ ϕ)

-- ϕ is valid if it holds in all models
def valid (ϕ : Formula) : Prop :=
  ∀ {World : Type} (M : Model World), models M ϕ
notation:30 " ⊨ " ϕ:30 => valid ϕ

end Reduct

/-══════════════════════════════════════════════════════════════════
  Proof System for the Closure
══════════════════════════════════════════════════════════════════-/
namespace Closure

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

| know_Oper {ϕ} :
    prove ϕ
    ----------------
  → prove (□ ϕ)

-- Propositional Axioms
| prop_self  {ϕ}     : prove (ϕ ⟶ ϕ)
| prop_intro {ϕ ψ}   : prove (ϕ ⟶ (ψ ⟶ ϕ))
| prop_distr {ϕ ψ ρ} : prove ((ϕ ⟶ (ψ ⟶ ρ)) ⟶ ((ϕ ⟶ ψ) ⟶ (ϕ ⟶ ρ)))
| contrapos  {ϕ ψ}   : prove ((not ϕ ⟶ not ψ) ⟶ (ψ ⟶ ϕ))

-- Axioms for □
| distr {ϕ ψ} : prove (□ (ϕ ⟶ ψ) ⟶ (□ ϕ ⟶ □ ψ))

-- Axioms for □∗
| mix       {ϕ} : prove (□∗ ϕ ⟶ (ϕ and □ □∗ ϕ))
| induction {ϕ} : prove ((ϕ and □∗(ϕ ⟶ □ ϕ)) ⟶ □∗ ϕ)
notation:30 " ⊢ " ϕ:30 => prove ϕ

end Closure

/-══════════════════════════════════════════════════════════════════
  Proof System for the Reduction
══════════════════════════════════════════════════════════════════-/
namespace Reduct

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

| know_Oper {ϕ} :
    prove ϕ
    ----------------
  → prove (□ ϕ)

-- Propositional Axioms
| prop_self  {ϕ}     : prove (ϕ ⟶ ϕ)
| prop_intro {ϕ ψ}   : prove (ϕ ⟶ (ψ ⟶ ϕ))
| prop_distr {ϕ ψ ρ} : prove ((ϕ ⟶ (ψ ⟶ ρ)) ⟶ ((ϕ ⟶ ψ) ⟶ (ϕ ⟶ ρ)))
| contrapos  {ϕ ψ}   : prove ((not ϕ ⟶ not ψ) ⟶ (ψ ⟶ ϕ))

-- Axioms for □
| distr {ϕ ψ} : prove (□ (ϕ ⟶ ψ) ⟶ (□ ϕ ⟶ □ ψ))
| refl  {ϕ}   : prove (□ ϕ ⟶ ϕ)
| trans {ϕ}   : prove (□ ϕ ⟶ □ □ ϕ)

-- Axioms for □⁻
-- These are exactly the same as the axioms for □∗,
-- except we replace
--     □∗ ⤳  □
--     □  ⤳  □⁻
| mix       {ϕ} : prove (□ ϕ ⟶ (ϕ and □⁻ □ ϕ))
| induction {ϕ} : prove ((ϕ and □(ϕ ⟶ □⁻ ϕ)) ⟶ □ ϕ)
notation:30 " ⊢ " ϕ:30 => prove ϕ

end Reduct

/-══════════════════════════════════════════════════════════════════
  Soundness for the Closure
══════════════════════════════════════════════════════════════════-/
namespace Closure

-- Semantic statement of modus ponens.
-- (It's convenient to have it as a seperate lemma.)
--------------------------------------------------------------------
lemma models_modpon {M : Model World} {ϕ ψ : Formula} :
    models M ϕ
  → models M (ϕ ⟶ ψ)
    ----------------
  → models M ψ := by
--------------------------------------------------------------------
  intro h₁ h₂
  simp [models, satisfies] at h₂
  intro w
  exact h₂ w (h₁ w)

-- Soundness: If we can prove ϕ from nothing (just our proof rules alone),
-- then ϕ holds in every neural network model.
--------------------------------------------------------------------
theorem soundness : ∀ (ϕ : Formula),
  ⊢ ϕ → ⊨ ϕ := by
--------------------------------------------------------------------
  intro ϕ h₁ World M

  -- We case on each of our proof rules and axioms
  induction h₁
  -- Proof Rules
  case modpon ϕ ψ _ _ IH₂ IH₃ => exact models_modpon IH₂ IH₃

  case know_Oper ϕ h IH =>
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
    apply by_contradiction
    exact fun h => h₁ h h₂

  -- Axioms for □
  case distr ϕ ψ =>
    simp [models, satisfies]
    intro w h₁ h₂ u h₃
    exact h₁ _ (h₂ _ h₃) h₃

  -- Axioms for □∗
  case mix ϕ =>
    simp [models, satisfies]
    intro w h₁
    -- TODO: Check soundness of Mix!  (I did it on paper)
    sorry

  case induction ϕ =>
    -- TODO: Check soundness of Induction!  (I did it on paper)
    sorry

end Closure

/-══════════════════════════════════════════════════════════════════
  Soundness for the Reduction
══════════════════════════════════════════════════════════════════-/
namespace Reduct

-- Semantic statement of modus ponens.
-- (It's convenient to have it as a seperate lemma.)
--------------------------------------------------------------------
lemma models_modpon {M : Model World} {ϕ ψ : Formula} :
    models M ϕ
  → models M (ϕ ⟶ ψ)
    ----------------
  → models M ψ := by
--------------------------------------------------------------------
  intro h₁ h₂
  simp [models, satisfies] at h₂
  intro w
  exact h₂ w (h₁ w)

-- Soundness: If we can prove ϕ from nothing (just our proof rules alone),
-- then ϕ holds in every neural network model.
--------------------------------------------------------------------
theorem soundness : ∀ (ϕ : Formula),
  ⊢ ϕ → ⊨ ϕ := by
--------------------------------------------------------------------
  intro ϕ h₁ World M

  -- We case on each of our proof rules and axioms
  induction h₁
  -- Proof Rules
  case modpon ϕ ψ _ _ IH₂ IH₃ => exact models_modpon IH₂ IH₃

  case know_Oper ϕ h IH =>
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
    apply by_contradiction
    exact fun h => h₁ h h₂

  -- Axioms for □
  case distr ϕ ψ =>
    simp [models, satisfies]
    intro w h₁ h₂ u h₃
    exact h₁ _ (h₂ _ h₃) h₃

  case refl ϕ =>
    simp [models, satisfies]
    intro w h₁
    exact h₁ w (M.refl w)

  case trans ϕ =>
    simp [models, satisfies]
    intro w h₁ u h₂ v h₃
    exact h₁ _ (M.trans h₂ h₃)

  -- Axioms for □⁻
  case mix ϕ =>
    simp [models, satisfies]
    intro w h₁
    -- TODO: Check soundness of Mix!  (I did it on paper)
    -- We need the right properties for the *reduction* instead
    -- of the closure!
    sorry

  case induction ϕ =>
    -- TODO: Check soundness of Induction! (I did it on paper)
    -- We need the right properties for the *reduction* instead
    -- of the closure!
    sorry

end Reduct

/-══════════════════════════════════════════════════════════════════
  Building Models for □, □⁻ from Models for □, □∗
══════════════════════════════════════════════════════════════════-/

-- Syntactic translation to build ϕ∗ from ϕ⁻
def Reduct.Formula.transl : Reduct.Formula → Closure.Formula := fun
| pᵖ => pᵖ
| ⊤ => ⊤
| not ϕ => not ϕ.transl
| ϕ and ψ => ϕ.transl and ψ.transl
| □ ϕ => □∗ ϕ.transl
| □⁻ ϕ => □ ϕ.transl

def Closure.Model.toReduct (M : Closure.Model World) : Reduct.Model World :=
{ Edge := Relation.ReflTransGen M.Edge
  proposition_eval := M.proposition_eval
  worlds := M.worlds

  -- Note that the input model is not necessarily reflexive
  -- and transitive.  But since Edge is the refl-trans closure
  -- of M.Edge, *this* model is reflexive and transitive.
  refl := IsRefl.reflexive
  trans := transitive_of_trans (Relation.ReflTransGen M.Edge)
}

-- This is the big theorem, which lets us inherit
-- completeness for the □, □⁻ language from
-- completeness for the □, □∗ language.
-- (First, translate the ϕ⁻ formula to a ϕ∗ formula,
--  build a model M for it, and build a model M.toReduct for that.)
--------------------------------------------------------------------
theorem toReduct_homomorphism {M : Closure.Model World} {ϕ : Reduct.Formula} {w : World} :
  (M.toReduct; w ⊩ ϕ) ↔ (M; w ⊩ ϕ.transl) := by
--------------------------------------------------------------------
  induction ϕ generalizing w

  case proposition p =>
    simp only [Reduct.satisfies, Closure.satisfies]
    simp only [Closure.Model.toReduct]

  case top =>
    simp only [Reduct.satisfies, Closure.satisfies]

  case _ ϕ IH =>
    simp only [Reduct.satisfies, Closure.satisfies]
    sorry

  case _ ϕ ψ IH₁ IH₂ => exact and_congr IH₁ IH₂

  case Oper ϕ IH =>
    sorry

  case Reduct ϕ IH =>
    sorry

--------------------------------------------------------------------
theorem toReduct_models {ϕ : Reduct.Formula} :
  ⊨ ϕ ↔ ⊨ ϕ.transl := by
--------------------------------------------------------------------
  simp only [Closure.valid, Closure.models, Reduct.valid, Reduct.models]
  apply Iff.intro
  case mp => exact fun h₁ World M w => toReduct_homomorphism.mp sorry
  case mpr => exact fun h₁ World M w => sorry -- toReduct_homomorphism.mpr sorry
