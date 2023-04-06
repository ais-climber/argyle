import Mathlib

-- Minimum working example for a question about convert

-- Tactic proof
example (x y : α) (Pred : α → Prop) (f g h : α → α) : 
  x = y
  → Pred (f (g (h x)))
  → Pred (f (g (h y))) := by

  intro h₁ h₂
  convert h₂ using 4
  exact symm h₁
