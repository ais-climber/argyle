import Mathlib
import Mathlib.Algebra.Parity

def weighted_sum_even (x₁ x₂ w₁ w₂ : ℕ) : Prop :=
  let term₁ := x₁ * w₁
  let term₂ := x₂ * w₂
  Even (term₁ + term₂)

example {x₁ x₂ w₁ w₂ : ℕ} 
  (h₁ : x₁ = x₂) (h₂ : w₁ = w₂) : 
  weighted_sum_even x₁ x₂ w₁ w₂
  → weighted_sum_even x₂ x₁ w₂ w₁ := by

  intro h₁
  unfold weighted_sum_even
  unfold weighted_sum_even at h₁
  
  -- I can eliminate the 'let' in the goal using intro
  intro term₂₁
  intro term₂₂
  
  -- But I don't know how to "intro at h₁"
  let term₁₁ := x₁ * w₁
  let term₁₂ := x₂ * w₂;
  have h₃ : Even (term₁₁ + term₁₂) := h₁
  sorry

