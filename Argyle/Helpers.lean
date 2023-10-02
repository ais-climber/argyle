import Mathlib.Data.List.Sigma
import Mathlib.Data.Real.Basic

-------------------------------------------------
-- Helper functions and lemmas
-------------------------------------------------

-- This isn't in the standard library, but essentially it says:
-- If we treat xs like an association list, and we *don't*
-- change the indices, lookup after mapping f to the outputs 
-- is the same as applying f to the original lookup.
--------------------------------------------------------------------
theorem lookup_map (xs : List ((ℕ × ℕ) × ℚ)) (a : ℕ × ℕ) (f : ((ℕ × ℕ) × ℚ) → ℚ) :
  List.lookup a (List.map (fun x => (x.1, f x)) xs) = 
    match List.lookup a xs with
    | some v => f (a, v)
    | none => none := by
--------------------------------------------------------------------
  induction xs
  case nil => simp
  case cons x xs IH =>
    simp only [List.map, List.lookup]

    -- Break up the inner match statements, and apply our IH!
    by_cases (a = x.fst)
    case pos => simp [h]
    case neg =>
      have h₁ : (a == x.fst) = false := by
        apply Classical.byContradiction
        intro hcontr
        exact absurd (eq_of_beq (eq_true_of_ne_false hcontr)) h
      
      simp [h₁]
      exact IH

-- This should *also* be in the standard library, but isn't!
--------------------------------------------------------------------
theorem lookup_mem (xs : List (ℕ × ℕ)) (a b : ℕ) :
  (List.lookup a xs = some b) → (a, b) ∈ xs := by
--------------------------------------------------------------------
  intro h₁

  induction xs
  case nil => simp at h₁
  case cons x xs IH => 
    simp only [List.lookup] at h₁

    -- Split up the match!
    split at h₁
    case _ h₂ => 
      have h₃ : x = (a, b) := by
        rw [Prod.eq_iff_fst_eq_snd_eq]
        simp
        simp at h₁
        simp at h₂
        exact ⟨symm h₂, h₁⟩  

      rw [h₃]
      exact List.mem_cons_self _ _
    case _ _ => exact List.mem_cons_of_mem _ (IH h₁)

/-
List.lookup (m, n) net.graph.weights = none
-/

-- This should *also* be in the standard library, but isn't!
--------------------------------------------------------------------
theorem lookup_none (xs : List ((ℕ × ℕ) × ℚ)) (a : ℕ × ℕ) :
  (List.lookup a xs = none) → ∀ (b : ℚ), (a, b) ∉ xs := by
--------------------------------------------------------------------
  intro h₁ b

  induction xs
  case nil => simp
  case cons x xs IH => 
    simp only [List.lookup] at h₁
    
    -- Split up the match!
    split at h₁
    case _ h₂ => 
      intro hcontr
      sorry
      -- have h₃ : x = (a, b) := by
      --   rw [Prod.eq_iff_fst_eq_snd_eq]
      --   simp
      --   simp at h₁
      --   simp at h₂
      --   exact ⟨symm h₂, h₁⟩  

      -- rw [h₃]
      -- exact List.mem_cons_self _ _
    case _ h₂ => 
      intro hcontr
      rw [List.mem_cons] at hcontr

      -- We split; either (a, b) = x or (a, b) ∈ xs
      cases hcontr
      case inl h₃ => 
        simp at h₂
        have h₄ : b = x.2 := by
          apply symm
          apply Prod.snd_eq_iff.mpr
          apply symm
          sorry

        apply h₂
        apply symm
        apply Prod.fst_eq_iff.mpr
        apply symm
        rw [← h₄]
        exact h₃
        -- exact h₂ (symm (Prod.fst_eq_iff.mpr (symm _)))
        -- conv at h₂ =>
        --   simp; enter [1]
        --   rw [Prod.fst_eq_iff]
        -- simp at h₂

        -- -- rw [symm _ _] at h₂
        -- rw [Prod.fst_eq_iff] at h₂
        -- exact h₂ _
      case inr h₃ => exact IH h₁ h₃
      -- sorry -- exact List.mem_cons_of_mem _ (IH h₁)

-- I think this should be in the standard library, but it isn't.
-- It says: If every member of a sum is ≤ 0, then the whole sum is ≤ 0.
--------------------------------------------------------------------
theorem sum_le_zero {lst : List ℕ} {f : ℕ → ℚ} : 
  (∀ (a : ℕ), a ∈ lst → f a ≤ 0)
  → List.sum (List.map f lst) ≤ 0 := by
--------------------------------------------------------------------
  intro h₁
  induction lst
  case nil => rw [List.map_nil, List.sum_nil]
  case cons x xs IH => 
    simp only [List.map]
    rw [List.sum_cons]

    -- f(x) ≤ 0 and Sum(Map(xs)) ≤ 0,
    -- so their sum ≤ 0.
    have h₂ : f x ≤ 0 := by simp [h₁]
    have h₃ : ∀ (a : ℕ), a ∈ xs → f a ≤ 0 := by
      intro a ha
      simp [h₁, ha]

    exact add_nonpos h₂ (IH h₃)

--------------------------------------------------------------------
theorem sizeOf_erase (xs : List ℕ) (a : ℕ) : 
  sizeOf (List.erase xs a) ≤ sizeOf xs := by
--------------------------------------------------------------------
  induction xs
  case nil => simp [List.erase]
  case cons x xs IH => 
    simp only [List.erase]

    -- Split the match
    split
    case _ _ _ => simp
    case _ _ _ => simp [IH]

-- List.erase_of_not_mem is in the standard library,
-- but the other direction is not!
--------------------------------------------------------------------
theorem not_mem_of_erase {xs : List ℕ} {a : ℕ} : 
  (List.erase xs a) = xs → a ∉ xs := by
--------------------------------------------------------------------
  induction xs
  case nil => simp
  case cons x xs IH => 
    intro h₁
    simp only [List.erase] at h₁

    -- Split the match
    split at h₁
    case _ _ _ =>
      -- This case is impossible, since xs = x :: xs!
      exact absurd (symm h₁) (List.cons_ne_self x xs)
    case _ _ h₂ => 
      simp at h₁
      simp at h₂
      intro hcontr
      
      -- Either a = x or a ∈ xs. Either way we get a contradiction.
      cases (List.mem_cons).mp hcontr
      case inl h₃ => exact absurd (symm h₃) h₂
      case inr h₃ => exact absurd h₃ (IH h₁)

/-══════════════════════════════════════════════════════════════════
  Forward propagation in a net
══════════════════════════════════════════════════════════════════-/

-- I would like to write 
--     List.sum [w * x | for w in weights, for x in lst],
-- but list comprehensions are harder to reason about.
def weighted_sum (weights : List ℚ) (lst : List ℚ) : ℚ :=
  List.sum (List.zipWith (· * ·) weights lst)


#eval weighted_sum [] []
#eval weighted_sum [1] [3.0]
#eval weighted_sum [1, 2.0, 3.0] [5.0, 5.0, 5.0]

-- Not well-defined behavior (we expect the weights and lst to be of equal size,
-- but this is left implicit.)
#eval weighted_sum [1, 2.0] [3.0]

--------------------------------------------------------------------
lemma weighted_sum_eq (fw₁ fw₂ fx₁ fx₂ : ℕ → ℚ) (ls : List ℕ) :
  let x₁ : List ℚ := List.map (fun i => fx₁ i) (List.range ls.length)
  let x₂ : List ℚ := List.map (fun i => fx₂ i) (List.range ls.length)
  let w₁ : List ℚ := List.map (fun i => fw₁ i) (List.range ls.length)
  let w₂ : List ℚ := List.map (fun i => fw₂ i) (List.range ls.length)
  
  (∀ i, (fw₁ i) * (fx₁ i) = (fw₂ i) * (fx₂ i))
  → weighted_sum w₁ x₁ = weighted_sum w₂ x₂ := by
--------------------------------------------------------------------
  -- Simplify the weighted sum down to 
  -- fw₁ i * fx₁ j = fw₂ i * fx₂ j
  intro x₁ x₂ w₁ w₂ h₁
  simp only [weighted_sum]
  rw [List.zipWith_map_left]
  rw [List.zipWith_map_left]
  rw [List.zipWith_map_right]
  rw [List.zipWith_map_right]
  simp
  congr 2

  -- Now we just need to show 
  -- fw₁ i * fx₁ i = fw₂ i * fx₂ i,
  -- but this was exactly our assumption.
  exact funext fun i => h₁ i
  
--------------------------------------------------------------------
lemma weighted_sum_le (fw₁ fw₂ fx₁ fx₂ : ℕ → ℚ) (ls : List ℕ) :
  let x₁ : List ℚ := List.map (fun i => fx₁ i) (List.range ls.length)
  let x₂ : List ℚ := List.map (fun i => fx₂ i) (List.range ls.length)
  let w₁ : List ℚ := List.map (fun i => fw₁ i) (List.range ls.length)
  let w₂ : List ℚ := List.map (fun i => fw₂ i) (List.range ls.length)
  
  (∀ i, (fw₁ i) * (fx₁ i) ≤ (fw₂ i) * (fx₂ i))
  → weighted_sum w₁ x₁ ≤ weighted_sum w₂ x₂ := by
--------------------------------------------------------------------
  intro x₁ x₂ w₁ w₂ h₁
  simp only [weighted_sum]
  rw [List.zipWith_map_left]
  rw [List.zipWith_map_left]
  rw [List.zipWith_map_right]
  rw [List.zipWith_map_right]
  simp
  
  apply List.sum_le_sum
  intro m _
  exact h₁ m
  
-- WARNING:
-- This is actually FALSE!  For infinite sets, l[i] is not provably
-- in l (as far as I can figure.)
-- TODO: In the future, when making all this computable, I will
-- be using finite sets, and then I can use get instead of get!,
-- and get_mem in the standard library.
axiom get!_mem {α : Type} [Inhabited α] : 
  ∀ (l : List α) i, (l.get! i) ∈ l
