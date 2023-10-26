/-══════════════════════════════════════════════════════════════════
  Syntax for both Classical and Neural logics
══════════════════════════════════════════════════════════════════-/

namespace Syntax

inductive Formula : Type where
-- Propositional logic
| proposition : String → Formula
| top : Formula
| not : Formula → Formula
| and : Formula → Formula → Formula

-- "Possibly knows" and "Possibly finds typical of" modalities
| Know : Formula → Formula
| Typ : Formula → Formula

postfix:max "ᵖ"     => Formula.proposition
notation    "⊤"     => Formula.top
prefix:85   "[K] "  => Formula.Know
prefix:85   "[T] "  => Formula.Typ
prefix:75   "not "  => Formula.not
infixl:65   " and " => Formula.and

-- Abbreviations
def Formula.diaKnow : Formula → Formula := fun ϕ => not [K] (not ϕ)
def Formula.diaTyp : Formula → Formula := fun ϕ => not [T] (not ϕ)
def Formula.or : Formula → Formula → Formula := fun ϕ ψ => (not ((not ϕ) and (not ψ)))
def Formula.implies : Formula → Formula → Formula := fun ϕ ψ => or (not ϕ) ψ
def Formula.iff : Formula → Formula → Formula := fun ϕ ψ => (implies ϕ ψ) and (implies ψ ϕ)
def Formula.conditional : Formula → Formula → Formula := fun ϕ ψ => implies ([T] ϕ) ψ

prefix:85   "⟨K⟩ "  => Formula.diaKnow
prefix:85   "⟨T⟩ "  => Formula.diaTyp
infixl:60   " or " => Formula.or
infixl:57   " ⟶ " => Formula.implies
infixl:55   " ⟷ " => Formula.iff
infixl:57   " ⟹ " => Formula.conditional

-- Some sanity checks
#check [K] "a"ᵖ ⟹ "b"ᵖ and [T] "c"ᵖ

end Syntax
