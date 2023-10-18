import Argyle.Net
import Argyle.Operators.Reachable
import Argyle.Operators.Reachedby
open Set
open Classical

variable (net : Net)

-- FORWARD PROPAGATION IN A NET
-- By recursion on the layers of our feedforward network.
-- (_acc indicates that we are using the layer as an accumulator
--  to do recursion.)
-- 
-- n ∈ propagate_acc(S) iff either:
--   Base Case (L=0): n ∈ S
--   Rcrs Case (L≥0): n ∈ S, or the nodes m preceding n activate n.
--     (We check their activation values via propagate_acc on m)
-- 
-- TODO: Make this computable!!!
-- change return type to 'Bool' instead of 'Prop'
-- and change 'Set' to be a finite set
-- and change net.graph to be finite as well!
-- 
-- Then unit-test all this with #eval!
-- 
-- NOTE: Although 'do' notation might be more readable here,
--       I avoid it because it's hard to reason about.
@[simp]
def propagate_acc (net : Net) (S : Set ℕ) (n : ℕ) (L : ℕ) : Prop :=
  match L with
  | Nat.zero => n ∈ S
  | Nat.succ _ =>
    let preds := preds net n
    let prev_activ := List.map (fun i => 
      let m := preds.get! i
      if propagate_acc net S m (layer net m) then 1 else 0) 
        (List.range preds.length)
    n ∈ S ∨ activ net prev_activ n
termination_by propagate_acc net S n L => layer net n
decreasing_by exact layer_preds net m n (get!_mem preds i)

-- Set variation of propagate
def propagate (net : Net) (S : Set ℕ) : Set ℕ :=
  fun n => propagate_acc net S n (layer net n)

-------------------------------------------------
-- Some helper lemmas
-- (just to clean up the monstrous proofs ahead!)
-- 
-- TODO: Clean these up with nicer @simp lemmas about
-- propagate and activ
-------------------------------------------------

--------------------------------------------------------------------
lemma simp_propagate_acc (net : Net) :
  n ∉ S
  → propagate_acc net S n (Nat.succ L) =
  let preds := preds net n
  let prev_activ := List.map (fun i => 
    let m := preds.get! i
    if propagate_acc net S m (layer net m) then 1 else 0) 
      (List.range preds.length)
  activ net prev_activ n := by
--------------------------------------------------------------------
  intro (h₁ : n ∉ S)
  apply Iff.to_eq
  apply Iff.intro

  case mp => 
    intro h₂
    simp only [propagate_acc]
    simp only [propagate_acc] at h₂
    
    cases h₂
    case inl h₃ => contradiction
    case inr h₃ => exact h₃ 
  
  case mpr => 
    intro h₂
    simp only [propagate_acc]
    simp only [propagate_acc] at h₂
    exact Or.inr h₂


-- If A and B agree on all the predecessors of n, then they agree on n.
-- This lemma is extremely inefficient to use.  In order to make it
-- remotely usable, we've simplified everything down to unreadable
-- garbage.  In order to make use of it, I recommend:
--   - Applying 'simp' to your 'activ' hypotheses (get rid of any let's)
--   - Use 'exact' instead of 'apply' (exit tactic mode)
-- 
--------------------------------------------------------------------
lemma activ_agree (net : Net) (A B : Set ℕ) (n : ℕ) :
  (∀ (m : ℕ), m ∈ preds net n → (m ∈ A ↔ m ∈ B))
  → activ net (List.map (fun i => 
      let m := (preds net n).get! i
      if A m then 1 else 0) 
        (List.range (preds net n).length)) n
  → activ net (List.map (fun i => 
      let m := (preds net n).get! i
      if B m then 1 else 0) 
        (List.range (preds net n).length)) n := by
--------------------------------------------------------------------
  intro h₁ h₂
  simp only [activ]
  simp only [activ] at h₂
  convert ← h₂ using 6

  rename_i i
  let m := (preds net n).get! i
  have h₃ : m ∈ (preds net n) := get!_mem (preds net n) i
  exact h₁ m h₃

/-══════════════════════════════════════════════════════════════════
  Properties of Propagation
══════════════════════════════════════════════════════════════════-/

--------------------------------------------------------------------
lemma prop_layer_zero (net : Net) : ∀ (S : Set ℕ) (n : ℕ),
  layer net n = 0
  → n ∈ propagate net S
  → n ∈ S := by
--------------------------------------------------------------------
  intro (S : Set ℕ) (n : ℕ)
        (hL : layer net n = 0)
        (h₁ : n ∈ propagate net S)

  simp only [propagate, Membership.mem, Set.Mem] at h₁
  rw [hL] at h₁
  simp only [propagate_acc] at h₁
  exact h₁

--------------------------------------------------------------------
theorem propagate_is_extens : 
  ∀ (S : Set ℕ),
  S ⊆ propagate net S := by
--------------------------------------------------------------------
  intro (S : Set ℕ)
        (n : ℕ) (h₁ : n ∈ S)
  simp only [Membership.mem, Set.Mem, propagate]

  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L

  -- Base Step
  case zero => 
    simp only [propagate_acc]
    exact h₁
  
  -- Inductive Step
  case succ k _ => 
    simp only [propagate_acc]
    exact Or.inl h₁

-- Corollary: The same statement, but for propagate_acc
-- (this is a helper lemma for the properties that follow.)
-------------------------------------------------
lemma propagate_acc_is_extens :
  ∀ (S : Set ℕ),
  n ∈ S → propagate_acc net S n (layer net n) := by
-------------------------------------------------
  intro (S : Set ℕ)
  intro (h₁ : n ∈ S)
  have h₂ : n ∈ propagate net S := propagate_is_extens _ _ h₁
  simp only [Membership.mem, Set.Mem, propagate] at h₂
  exact h₂
  

--------------------------------------------------------------------
theorem propagate_is_idempotent : 
  ∀ (S : Set ℕ),
  propagate net S = 
    propagate net (propagate net S) := by
--------------------------------------------------------------------
  intro (S : Set ℕ)
  apply ext
  intro (n : ℕ)
  simp only [Membership.mem, Set.Mem, propagate]

  -- By strong induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n

  -- Base Step
  case hz =>
    simp only [Membership.mem, Set.Mem, propagate_acc]
    conv in (layer net n) => rw [hL]
    simp only [propagate_acc]
    exact ⟨fun x => x, fun x => x⟩
  
  -- Inductive Step
  case hi L IH =>
    apply Iff.intro
    
    -- Forward direction is easy, just apply extensive
    case mp =>
      intro h₁
      rw [symm hL]
      rw [symm hL] at h₁
      exact @propagate_acc_is_extens net _ _ h₁

    -- Backwards direction is trickier
    case mpr => 
      intro h₁
      
      -- By cases; either n ∈ S or n ∉ S
      -- Again; either n ∈ propagate S or n ∉ propagate S 
      by_cases n ∈ S
      case pos => 
        rw [symm hL]
        exact @propagate_acc_is_extens net _ _ h
      case neg => 
        by_cases propagate_acc net S n (layer net n)
        case pos => 
          rw [symm hL]
          exact h
        case neg =>
          -- Just some simplifications and rewriting definitions
          rename_i n_not_in_S
          rw [simp_propagate_acc net n_not_in_S]
          
          have h₂ : ¬n ∈ propagate net S := h
          simp [propagate] at h₂
          rw [simp_propagate_acc net h₂] at h₁

          -- We abbreviate the two 'simp'ed sets for convenience.
          let S₁ := fun m => propagate_acc net (fun n => 
            propagate_acc net S n (layer net n)) m (layer net m)
          let S₂ := fun m => propagate_acc net S m (layer net m)
          
          -- Apply IH to the predecessors
          have h₂ : ∀ (m : ℕ), m ∈ preds net n → (S₁ m ↔ S₂ m) := by
            simp only [Membership.mem] -- really just want to unfold the let
            intro m hm
            generalize hLm : layer net m = Lm
            have h₃ : Lm ≤ L := by
              rw [symm hLm]
              apply Nat.lt_succ.mp
              rw [symm hL]
              exact layer_preds net m n hm
            exact (symm (IH Lm h₃ m hLm).to_eq).to_iff

          -- Apply the activ_agree lemma
          simp only [preds]
          simp only [preds] at h₁
          exact activ_agree _ S₁ S₂ _ h₂ h₁


-- This is essentially Hannes' proof.
-- TODO: For consistency's sake, replace inner proof with
--   application of 'activ_agree'
--------------------------------------------------------------------
theorem propagate_is_cumulative :
  ∀ (A B : Set ℕ), A ⊆ B
  → B ⊆ propagate net A
  → propagate net A = propagate net B := by
--------------------------------------------------------------------
  intro (A : Set ℕ) (B : Set ℕ)
        (h₁ : A ⊆ B)
        (h₂ : B ⊆ propagate net A)
  apply ext
  intro (n : ℕ)
  simp only [Membership.mem, Set.Mem, propagate]
  simp only [Membership.mem, Set.Mem, propagate] at h₂

  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n

  -- Base Step
  case hz =>
    simp only [propagate_acc]
    apply Iff.intro
    case mp => exact fun h₃ => h₁ h₃
    case mpr =>
      intro h₃
      have h₄ : propagate_acc net A n (layer net n) := h₂ h₃
      conv at h₄ in (layer net n) => rw [hL]
      simp only [propagate_acc] at h₄
      exact h₄

  -- Inductive Step
  case hi k IH => 
    apply Iff.intro

    -- Forward Direction
    case mp => 
      intro h₃

      -- By cases; either n ∈ B or n ∉ B.
      -- Similarly, either n ∈ A or n ∉ A. 
      by_cases n ∈ B
      case pos =>
        rw [symm hL]
        exact @propagate_acc_is_extens net _ _ h -- TODO: replace acc variation
      case neg =>
        by_cases n ∈ A
        case pos => 
          rename_i n_not_in_B 
          exact absurd (h₁ h) n_not_in_B
        case neg => 
          -- Just some simplifications and rewriting definitions
          rename_i n_not_in_B
          rw [simp_propagate_acc net h] at h₃
          rw [simp_propagate_acc net n_not_in_B]

          -- Just try to prove it and turn it into an 'activ_agree'
          -- lemma later!
          -- Go into 'prev_activ' and substitute using our IH.
          -- Then try to prove what's left.
          simp
          simp at h₃
          convert h₃ using 4
          rename_i i
          generalize hm : List.get! (net.graph.predecessors n) i = m
          generalize hLm : layer net m = Lm

          -- Apply the inductive hypothesis!
          have h₃ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (net.graph.predecessors n) i
          have h₄ : Lm ≤ k := by 
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            exact layer_preds net m n h₃
          exact (symm (IH Lm h₄ m hLm).to_eq).to_iff

    -- Backwards Direction (should be very similar)
    case mpr => 
      intro h₃

      -- By cases; either n ∈ A or n ∉ A
      by_cases n ∈ A
      case pos => 
        rw [symm hL]
        exact @propagate_acc_is_extens net _ _ h -- TODO: replace acc variation
      case neg => 
        by_cases n ∈ B
        case pos => 
          rename_i n_not_in_A
          rw [symm hL]
          exact h₂ h
        case neg => 
          -- Just some simplifications and rewriting definitions
          rename_i n_not_in_A
          rw [simp_propagate_acc net h] at h₃
          rw [simp_propagate_acc net n_not_in_A]

          -- Just try to prove it and turn it into an 'activ_agree'
          -- lemma later!
          -- Go into 'prev_activ' and substitute using our IH.
          -- Then try to prove what's left.
          simp
          simp at h₃
          convert h₃ using 4
          rename_i i
          generalize hm : List.get! (net.graph.predecessors n) i = m
          generalize hLm : layer net m = Lm

          -- Apply the inductive hypothesis!
          have h₃ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (net.graph.predecessors n) i
          have h₄ : Lm ≤ k := by 
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            exact layer_preds net m n h₃
          exact IH Lm h₄ m hLm

/-══════════════════════════════════════════════════════════════════
  Reach-Prop Interaction Properties
══════════════════════════════════════════════════════════════════-/

--------------------------------------------------------------------
lemma minimal_cause_helper (net : Net) : ∀ (A B : Set ℕ), ∀ (n : ℕ),
  n ∈ reachedby net B
  → (n ∈ propagate net A
  ↔ n ∈ propagate net (A ∩ reachedby net B)) := by
--------------------------------------------------------------------
  intro (A : Set ℕ) (B : Set ℕ)
  intro (n : ℕ)
  intro (h₁ : n ∈ reachedby net B)
  simp only [Membership.mem, Set.Mem, propagate]

  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n
  
  -- Base Step
  case hz => 
    apply Iff.intro
    case mp => 
      intro h₂
      simp only [propagate_acc]
      simp only [propagate_acc] at h₂
      exact ⟨h₂, h₁⟩

    case mpr => 
      intro h₂
      simp only [propagate_acc]
      simp only [propagate_acc] at h₂
      exact h₂.1

  -- Inductive Step
  case hi k IH => 
    apply Iff.intro

    -- Forward Direction
    case mp => 
      intro h₂

      -- By cases; either n ∈ A or not.
      by_cases n ∈ A
      case pos => 
        -- This case is trivial (just apply Extens)
        rw [symm hL]
        have h₃ : n ∈ A ∩ reachedby net B := ⟨h, h₁⟩ 
        exact @propagate_acc_is_extens net _ _ h₃
      case neg => 
        -- If n ∉ A, then n ∉ A ∩ reachedby net B
        have h₃ : n ∉ A ∩ reachedby net B := 
          fun n_in_A => absurd n_in_A.1 h
        
        -- Just some simplifications and rewriting definitions
        rw [simp_propagate_acc net h] at h₂
        rw [simp_propagate_acc net h₃]

        -- TODO: This is the stuff that should go in the activ_agree lemma!
        simp
        simp at h₂
        convert h₂ using 4
        rename_i i
        generalize hm : List.get! (preds net n) i = m
        generalize hLm : layer net m = Lm

        -- Apply the inductive hypothesis!
        have h₄ : m ∈ preds net n := by
          rw [symm hm]
          simp [preds]
          exact get!_mem (preds net n) i
        have h₅ : Lm ≤ k := by
          rw [symm hLm]
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact layer_preds net m n h₄
        have h₆ : m ∈ reachedby net B :=
          match h₁ with
          | ⟨x, hx⟩ => ⟨x, ⟨hx.1, Graph.Path_trans _ (Path_of_preds _ h₄) hx.2⟩⟩ -- (preds_path _ h₄)
        exact (symm (IH Lm h₅ m h₆ hLm).to_eq).to_iff

    -- Backwards Direction (should be similar)
    case mpr =>
      intro h₂

      -- By cases; either n ∈ A or not.
      by_cases n ∈ A
      case pos => 
        -- This case is trivial (just apply Extens)
        rw [symm hL]
        exact @propagate_acc_is_extens net _ _ h
      case neg => 
        -- If n ∉ A, then n ∉ A ∩ reachedby net B
        have h₃ : n ∉ A ∩ reachedby net B := 
          fun n_in_A => absurd n_in_A.1 h
        
        -- Just some simplifications and rewriting definitions
        rw [simp_propagate_acc net h₃] at h₂
        rw [simp_propagate_acc net h]

        -- TODO: This is the stuff that should go in the activ_agree lemma!
        simp
        simp at h₂
        convert h₂ using 4
        rename_i i
        generalize hm : List.get! (preds net n) i = m
        generalize hLm : layer net m = Lm

        -- Apply the inductive hypothesis!
        have h₄ : m ∈ preds net n := by
          rw [symm hm]
          simp [preds]
          exact get!_mem (preds net n) i
        have h₅ : Lm ≤ k := by
          rw [symm hLm]
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact layer_preds net m n h₄
        have h₆ : m ∈ reachedby net B :=
          match h₁ with
          | ⟨x, hx⟩ => ⟨x, ⟨hx.1, Graph.Path_trans _ (Path_of_preds _ h₄) hx.2⟩⟩
        exact IH Lm h₅ m h₆ hLm


-- This is the actual property I want.
-- If A => B is the conditional Best(A) -> B, this corresponds
-- to the following axiom:
-- 
--    A => B    iff    A ∨ K↓(B) => B
-- 
-- (how should we interpret K↓???)
--------------------------------------------------------------------
theorem minimal_cause (net : Net) : ∀ (A B : Set ℕ),
  B ⊆ propagate net A
  ↔ B ⊆ propagate net (A ∩ reachedby net B) := by
--------------------------------------------------------------------
  intro (A : Set ℕ) (B : Set ℕ)
  apply Iff.intro
  case mp => exact fun h₁ n h₂ => (minimal_cause_helper net _ _ _ 
    (reachedby_is_extens _ _ h₂)).mp (h₁ h₂)
  case mpr => exact fun h₁ n h₂ => (minimal_cause_helper net _ _ _ 
    (reachedby_is_extens _ _ h₂)).mpr (h₁ h₂)