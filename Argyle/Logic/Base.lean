import Argyle.Net
import Argyle.Operators.Reachable
import Argyle.Operators.Propagate

/-══════════════════════════════════════════════════════════════════
  Syntax
══════════════════════════════════════════════════════════════════-/

inductive Formula : Type where
-- Propositional logic
| proposition : String → Formula
| not : Formula → Formula
| and : Formula → Formula → Formula

-- "Possibly knows" and "Possibly finds typical of" modalities
| diaKnow : Formula → Formula
| diaTyp : Formula → Formula

postfix:max "ᵖ"   => Formula.proposition
prefix:85   "⟨K⟩ " => Formula.diaKnow
prefix:85   "⟨T⟩ " => Formula.diaTyp
prefix:75   "not "   => Formula.not
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
| not ϕ => (interpret net ϕ)ᶜ
| ϕ and ψ => (interpret net ϕ) ∩ (interpret net ψ)
| ⟨K⟩ ϕ => reachable net (interpret net ϕ)
| ⟨T⟩ ϕ => propagate net (interpret net ϕ)

-- Relation for "net satisfies ϕ at point n"
def satisfies (net : Net) (ϕ : Formula) (n : ℕ) : Prop :=
  n ∈ interpret net ϕ
notation:35 net:40 ", " n:40 " ⊩ " ϕ:40 => satisfies net ϕ n

-- Relation for "net models ϕ" (at *all* points!)
def models (net : Net) (ϕ : Formula) : Prop :=
  ∀ n, (net, n ⊩ ϕ)
notation:30 net:40 " ⊨ " ϕ:40 => models net ϕ


/-══════════════════════════════════════════════════════════════════
  Proof System
══════════════════════════════════════════════════════════════════-/

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

-- Notation for proves
notation:30 " ⊢ " ϕ:40 => prove ϕ

/-
infix 5 ⊢_

-----------------------------
-- Def: ⊢
-----------------------------
data ⊢_ : Formula → Set where
  ------------- Prop. logic axioms
  ∧-I : ∀ {φ ψ}
    → ⊢ φ ⇒ (ψ ⇒ (φ ∧ ψ))
  

  ------------- Actual rules of the system
  -- Modus Ponens
  modpon : ∀ {φ ψ}
    → ⊢ φ
    → ⊢ φ ⇒ ψ
      ------------
    → ⊢ ψ

  -- Modal Necessitation
  necess : ∀ {φ x y}
    → ⊢ φ
      ------------
    → ⊢ [ x , y ] φ

  -- Equational
  eqn : ∀ {E}
    → ⊢ⱽ E
      ------------
    → ⊢ EQN E

  -- Static Logic Axioms
  weights : ∀ {w₁ w₂}
    → ⊢ (weights w₁ ∧ weights w₂) ⇒ EQN (w₁ ≡ⱽ w₂)
  sol : ∀ {x y₁ y₂}
    → ⊢ (sol x , y₁ ∧ sol x , y₂) ⇒ EQN (y₁ ≡ᴮ y₂)
  ex : ∀ {w}
    → ⊢ ◇ weights_ w
  -- a generalized version of the previous rule
  ex-general : ∀ {φ w}
    → ⊢ (weights_ w ⇒ φ) ⇒ ◇ φ
  
  -- NOT SOUND!
  --∃-uniq : ∀ {φ w}
  --  → ⊢ (◇ φ ∧ weights_ w) ⇒ (weights_ w ⇒ φ)

  cases : ∀ {x}
    → ⊢ sol x , bool false ∨ sol x , bool true

  out : ∀ {w x T}
    → ⊢ (weights_ w ∧ thres T) ⇒ 
          ((EQN (T <′ w ·ⱽ x) ⇒ sol x , bool true) ∧ (sol x , bool true ⇒ EQN (T <′ w ·ⱽ x)))
  -- TODO: Need to modify how we syntactically handle T

  -- Dynamic Logic Axioms
  ∧-dist→ : ∀ {φ ψ x y}
    → ⊢ [ x , y ] (φ ∧ ψ) ⇒ ([ x , y ] φ ∧ [ x , y ] ψ)
  ∧-dist← : ∀ {φ ψ x y}
    → ⊢ ([ x , y ] φ ∧ [ x , y ] ψ) ⇒ [ x , y ] (φ ∧ ψ)
  ⇒-dist→ : ∀ {φ ψ x y}
    → ⊢ [ x , y ] (φ ⇒ ψ) ⇒ ([ x , y ] φ ⇒ [ x , y ] ψ)
  ⇒-dist← : ∀ {φ ψ x y}
    → ⊢ ([ x , y ] φ ⇒ [ x , y ] ψ) ⇒ [ x , y ] (φ ⇒ ψ)
  
  generalize : ∀ {φ x y}
    → ⊢ [ x , y ] φ ⇒ ◇ φ
  dual : ∀ {φ x y}
    -- Note: this is only one direction of what is typically called "dual"
    → ⊢ ! ([ x , y ] (! φ)) ⇒ ◇ φ

  -- TODO: Handle addition syntactically
  obs : ∀ {w w⋆ x y y⋆ η}
    → ⊢ rate η ∧ (sol x , y⋆ ∧ EQN (w⋆ ≡ⱽ w +ⱽ (η *ⱽ (((cast y) -′ (cast y⋆)) *ⱽ x)))) 
      ⇒ (weights_ w ⇒ [ x , y ] weights_ w⋆)

-- I can't define this as a rule in the system
-- because it doesn't conclude ⊢ ...,
-- i.e. it is *actually* a rule about the *equational*
-- system
-- (or more accurately, a metarule about both.)
--
-- As it stands, I can't check the soundness of this rule,
-- since it's being expressed as a metarule...
postulate
  eqn₂ : ∀ {E}
      → ⊢ EQN E
        ------------
      → ⊢ⱽ E
-/

/-══════════════════════════════════════════════════════════════════
  Soundness
══════════════════════════════════════════════════════════════════-/

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
