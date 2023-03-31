import Mathlib.Tactic.LibrarySearch

-- Minimum working example for doing induction on
-- a more complicated expression

mutual def even odd
with even : ℕ → Bool
| 0     => tt
| (a+1) => odd a
with odd : ℕ → Bool
| 0     => ff
| (a+1) => even a