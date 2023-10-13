import Argyle.Net
import Argyle.Operators.Reachable
import Argyle.Operators.Propagate
import Argyle.Operators.Hebb
import Argyle.Logic.NeuralBase
import Mathlib.Data.Finset.Basic

import Mathlib.Tactic.LibrarySearch

/-══════════════════════════════════════════════════════════════════
  Syntax
══════════════════════════════════════════════════════════════════-/

-- The Logic of Hebbian Learning extends our base language
-- with a dynamic formula ⟨ϕ⟩_Hebb ψ
-- TODO: How do I inherit the rest of the static language?
--    i.e. all the connectives
inductive Formula' : Type where
-- Propositional logic
| static : Formula → Formula'
| hebbop : Formula' → Formula' → Formula'

postfix:max "ˢ"     => Formula'.static
notation:40 "⟨" ϕ "⟩_Hebb " ψ => Formula'.hebbop ϕ ψ

-- Here's an example of how we lift static formulas to
-- dynamic ones.
#check ⟨("a"ᵖ and "b"ᵖ)ˢ⟩_Hebb ([K] "a"ᵖ ⟶ "b"ᵖ and [T] "c"ᵖ)ˢ


/-══════════════════════════════════════════════════════════════════
  Semantics
══════════════════════════════════════════════════════════════════-/
-- As with the base logic, we use InterpretedNet as our models.

-- We extend our interpretation function to the new dynamic language.
def interpret' (Net : InterpretedNet) : Formula' → Set ℕ := fun
| ϕˢ => interpret Net ϕ
| ⟨ϕ⟩_Hebb ψ => 
  let UpdatedNet := { Net with 
    net := hebb_star Net.net (interpret' Net ϕ) }
  interpret' UpdatedNet ψ

notation:40 "⟦" ϕ "⟧'_" Net => interpret' Net ϕ

-- Semantics relations, lifted to the dynamic language
-- NOTE: Our convention is to mark these *dynamic versions* 
--    with an additional tick '.  This is somewhat subtle,
--    so please keep it in mind when reading these.
def satisfies' (Net : InterpretedNet) (ϕ : Formula') (n : ℕ) : Prop :=
  n ∈ (⟦ϕ⟧'_Net)
notation:35 net "; " n " ⊩' " ϕ => satisfies' net ϕ n

def models' (Net : InterpretedNet) (ϕ : Formula') : Prop :=
  ∀ n, (Net; n ⊩' ϕ)

def models_list' (Net : InterpretedNet) (Γ : List Formula') : Prop :=
  ∀ ϕ ∈ Γ, models' Net ϕ

def entails' (Γ : List Formula') (ϕ : Formula') : Prop :=
  ∀ (Net : InterpretedNet), models_list' Net Γ → models' Net ϕ 
notation:30 Γ:40 " ⊨' " ϕ:40 => entails' Γ ϕ


/-══════════════════════════════════════════════════════════════════
  Proof System
══════════════════════════════════════════════════════════════════-/

inductive prove' : Formula' → Prop where
-- Provable from static logic
-- TODO: Is this all we need?  Will this let us apply
--    static axioms to dynamic formulas??
| static {ϕ} :
    prove ϕ
    ----------------
  → prove' ϕˢ

-- Necessitation rule for ⟨ϕ⟩_Hebb
| know_necess {ϕ ψ} :
    prove' ψ
    ----------------
  → prove' (⟨ϕ⟩_Hebb ϕ)

-- Reduction Axioms
| hebb_prop  {P p : Formula}   : prove' (sorry)
| hebb_not   {P ϕ ψ : Formula} : prove' (sorry)
| hebb_and   {P ϕ ψ : Formula} : prove' (sorry)
| hebb_know  {P ϕ : Formula}   : prove' (sorry)
| hebb_typ   {P ϕ : Formula}   : prove' (sorry)

