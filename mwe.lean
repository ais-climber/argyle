import Mathlib

-- Minimum working example for a question about reasoning about
-- mutual inductive types

def f : Set ℕ → ℕ :=
  sorry

-- Either n ∈ S or 
inductive Propagation (net : BFNN) (S : Set ℕ) : ℕ → Prop where
  | in_signal : n ∈ S → Propagation net S n 
  | activ_by : 
    activ net {m | Propagation net S m} n → Propagation net S n 