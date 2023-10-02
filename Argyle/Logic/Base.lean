import Argyle.Operators.Reachable
import Argyle.Operators.Propagate

/-══════════════════════════════════════════════════════════════════
  Syntax
══════════════════════════════════════════════════════════════════-/

inductive Formula : Type where
  | proposition : String → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | diaKnow : Formula → Formula
  | diaTyp : Formula → Formula

postfix:max "ᵖ"   => Formula.proposition
prefix:85   "diaKnow " => Formula.diaKnow
prefix:85   "diaTyp " => Formula.diaTyp
prefix:75   "not "   => Formula.not
infixl:65   " and " => Formula.and

-- Abbreviations
notation:85 "Know " A:86 => not (diaKnow (not A))
notation:85 "Typ " A:86 => not (diaTyp (not A))
notation:65 A:85 " or " B:86 => (not A) and (not B)
notation:85 A:85 " ⟶ " B:86 => (not A) or B


example : Formula := Know "a"ᵖ ⟶ "b"ᵖ and Typ "c"ᵖ

-- infixl:65 " ⟨T⟩ " => HAdd.hAdd

/-
infix 13 EQN_
infix 11 sol_,_ weights_ thres_ rate_
infix 9 [_,_]_
infix 9 ◇_
infix 8 !_
infix 7 _∧_ _∨_
infix 6 _⇒_ -- Be careful!  This looks a lot like '→' !!!

-----------------------------
-- Def: Formula
-----------------------------
data Formula : Set where
  -- Include all vector space model formulas
  EQN_        : VSFormula → Formula

  -- Base formulas
  sol_,_     : VecTerm {N} → BoolTerm → Formula
  weights_   : VecTerm {N} → Formula
  thres_     : ScalarTerm → Formula
  rate_      : ScalarTerm → Formula

  -- Boolean connectives
  ⊥⁰      : Formula
  !_       : Formula → Formula
  _∧_      : Formula → Formula → Formula
  _∨_      : Formula → Formula → Formula
  _⇒_      : Formula → Formula → Formula

  -- Observation
  [_,_]_  : VecTerm {N} → BoolTerm → Formula → Formula

  -- A special existential modality  '◇ φ' 
  -- to be read "there exists a choice of weights w such that φ holds."
  ◇_     : Formula → Formula
-/

/-══════════════════════════════════════════════════════════════════
  Semantics
══════════════════════════════════════════════════════════════════-/

/-
infix 5 _,_⊨_
infix 5 ⊨_

-----------------------------
-- Def: Models
-----------------------------
-- We just specify the learning rate η and the threshold T.
-- The rest of the vector space model is just Agda's interpreter.
-- See vsm.agda for discussion on this.
Model : Set
Model = Float × Float

-- A dumb example of a model.
-- Sometimes any model whatsoever will suffice, and in this case
-- we use this one.
dummy-model : Model
dummy-model = ⟨ 0.0 , 0.0 ⟩

dummy-weight : Vec Float N
dummy-weight = {!   !}

-----------------------------
-- Def: ⊨
-----------------------------
-- TODO: Agda can't figure out that sol x , y⋆ is smaller than [ x , y ] φ.
--   So for now, I'll tell it that this does, in fact, terminate.
{-# TERMINATING #-}
_,_⊨_ : Model → Vec Float N → Formula → Set
-- vector space model case
M , w ⊨ EQN E  =    ⊨ⱽ E

-- sol case
⟨ η , T ⟩ , w ⊨ (sol x , y) = 
  y ≡ bool ⌊ T Data.Float.<? (vsm.dot-prod w (⟦ x ⟧ⱽ)) ⌋

-- weights case
M , w ⊨ weights w⋆ = 
  vec w ≡ w⋆
⟨ η , T ⟩ , w ⊨ thres T⋆ =
  scal T ≡ T⋆
⟨ η , T ⟩ , w ⊨ rate η⋆ =
  scal η ≡ η⋆

-- connectives
M , w ⊨ ⊥⁰ =        ⊥
M , w ⊨ ! φ =       ¬ M , w ⊨ φ
M , w ⊨ φ ∧ ψ =     (M , w ⊨ φ) × (M , w ⊨ ψ)
M , w ⊨ φ ∨ ψ =     (M , w ⊨ φ) ⊎ (M , w ⊨ ψ)
M , w ⊨ φ ⇒ ψ =     (M , w ⊨ φ) → (M , w ⊨ ψ)

-- observation case
⟨ η , T ⟩ , w ⊨ [ x , y ] φ =
  ∃[ w⋆ ] ∃[ y⋆ ] (⟨ η , T ⟩ , w ⊨ sol x , y⋆
     × (⟨ η , T ⟩ , w⋆ ⊨ φ)
     × ⊨ⱽ (vec w⋆ ≡ⱽ vec w +ⱽ (scal η *ⱽ (((cast y) -′ (cast y⋆)) *ⱽ x))))

-- existential case
M , w ⊨ ◇ φ =    ∃[ w⋆ ] (M , ⟦ w⋆ ⟧ⱽ ⊨ φ)

-----------------------------
-- Def: Validity
-----------------------------
⊨_ : Formula → Set
⊨_ φ = ∀ (M : Model) → 
  ∀ (w : Vec Float N) → 
    M , w ⊨ φ
-/


/-══════════════════════════════════════════════════════════════════
  Proof System
══════════════════════════════════════════════════════════════════-/

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
