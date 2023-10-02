import Mathlib.Data.Real.Basic

-------------------------------------------------
-- Activation functions
-------------------------------------------------
def binary_step (x : ℚ) : ℚ :=
  if x > 0 then 1 else 0

--------------------------------------------------------------------
theorem binary_step_is_binary (x : ℚ) :
    (binary_step x = 0) ∨ (binary_step x = 1) := by
--------------------------------------------------------------------
      -- simp [binary_step]

      cases (lt_or_ge 0 x) with

      -- Case 1: 0 < x
      | inl case1 =>
          have (h : binary_step x = 1) :=
            by
              simp only [binary_step]
              rw [(if_pos case1)]
          exact Or.inr h

      -- Case 2: ¬ (0 < x)
      | inr case2 =>
          have (h : binary_step x = 0) := 
            by 
              simp only [binary_step]
              rw [(if_neg (not_lt_of_le case2))]
          exact Or.inl h

-- Proof that binary_step is nondecreasing
-- This is also a 'hello world' to see if I can
-- reason about a branching program.
--------------------------------------------------------------------
theorem binary_step_nondecr (x₁ x₂ : ℚ) (hyp : x₁ ≤ x₂) :
  (binary_step x₁ ≤ binary_step x₂) := by
--------------------------------------------------------------------
    -- Simplify by applying the definition of binary_step.
    simp [binary_step]
    
    cases (lt_or_ge 0 x₁) with
    | inl case1 =>
      cases (lt_or_ge 0 x₂) with
      | inl case11 => 
          -- Both sides evaluate to 1,
          -- so we just prove that 1 ≤ 1.
          rw [(if_pos case1)]
          rw [(if_pos case11)]
      | inr case12 => 
          -- We have 0 < x₁ ≤ x₂ < 0,
          -- so this case is absurd. 
          exact absurd
            (lt_of_lt_of_le case1 hyp)
            (not_lt_of_le case12)
    | inr case2 => 
      cases (lt_or_ge 0 x₂) with
      | inl case21 => 
          -- We are in the second and first cases.
          rw [(if_neg (not_lt_of_le case2))]
          rw [(if_pos case21)]
          exact (le_of_lt rfl)
      | inr case22 => 
          rw [(if_neg (not_lt_of_le case2))]
          rw [(if_neg (not_lt_of_le case22))]
