import Mathlib

-- Minimum working example for a question about reasoning about 'do'

def lst : List ℕ := [1, 2, 3, 4, 5]

def evens : List Bool := do
  let n <- lst
  return Even n

example (n : ℕ) : evens.contains (Even n) → lst.contains n := by
  intro (h : evens.contains (Even n))
  sorry


